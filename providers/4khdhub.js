'use strict';

// ============================================================
// 4KHDHub Provider — Optimized Scraper
// ============================================================
// Key optimizations:
//  1. Persistent HTTP agent with keep-alive (connection reuse)
//  2. In-memory TTL cache (process-level, always active)
//  3. In-flight deduplication (concurrent requests for same URL share one fetch)
//  4. Pre-compiled regexes (no recompilation per call)
//  5. Proxy routing ONLY for hubcloud.cx (not for 4khdhub.fans)
//  6. Single-pass DOM parsing in extractHubCloud
//  7. Concurrency cap via p-limit (avoids flooding)
//  8. TMDB data accepted externally — skips duplicate API call when provided
// ============================================================

const axios        = require('axios');
const cheerio      = require('cheerio');
const bytes        = require('bytes');
const levenshtein  = require('fast-levenshtein');
const rot13Cipher  = require('rot13-cipher');
const { URL }      = require('url');
const http         = require('http');
const https        = require('https');

// ---------------------------------------------------------------------------
// Logging
// ---------------------------------------------------------------------------
const DEBUG   = process.env.DEBUG === 'true' || process.env['4KHDHUB_DEBUG'] === 'true';
const log     = DEBUG ? (...a) => console.log('[4KHDHub]', ...a)  : () => {};
const logWarn = DEBUG ? (...a) => console.warn('[4KHDHub]', ...a) : () => {};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------
const BASE_URL     = 'https://4khdhub.fans';
const TMDB_API_KEY = process.env.TMDB_API_KEY || '439c478a771f35c05022f9feabcca01c';
const SCRAPER_API_KEY = process.env.SCRAPER_API_KEY || null;

// Domains that block datacenter IPs — route through proxy
const PROXY_DOMAINS = new Set(['hubcloud.cx', 'hubcloud.lol', 'hubcloud.life']);

// Concurrency cap: max parallel HubCloud extractions
// Prevents flooding and avoids rate-limit bans
const HUBCLOUD_CONCURRENCY = 4;

// Inline semaphore (CJS-compatible, no ESM issues with p-limit v6)
function createLimiter(concurrency) {
    let active = 0;
    const queue = [];
    const next = () => {
        if (active >= concurrency || !queue.length) return;
        active++;
        const { fn, resolve, reject } = queue.shift();
        fn().then(resolve, reject).finally(() => { active--; next(); });
    };
    return fn => new Promise((resolve, reject) => { queue.push({ fn, resolve, reject }); next(); });
}
const limit = createLimiter(HUBCLOUD_CONCURRENCY);

// ---------------------------------------------------------------------------
// Pre-compiled regexes (compiled once, not inside hot paths)
// ---------------------------------------------------------------------------
const RE_SIZE          = /(\d+\.?\d*\s*[GM]B)/i;
const RE_HEIGHT        = /(\d{3,4})p/i;
const RE_REDIRECT_DATA = /'o','(.*?)'/;
const RE_VAR_URL       = /var\s+url\s*=\s*'([^']+)'/;
const RE_PXL_VAR       = /var\s+pxl\s*=\s*["'](https?:\/\/[^"']+)["']/i;

// ---------------------------------------------------------------------------
// HTTP Agents — persistent connection pools (reused across requests)
// ---------------------------------------------------------------------------
const httpAgent  = new http.Agent ({ keepAlive: true, maxSockets: 20, timeout: 20000 });
const httpsAgent = new https.Agent({ keepAlive: true, maxSockets: 20, timeout: 20000 });

// ---------------------------------------------------------------------------
// Axios instance — shared config, connection pool, full browser fingerprint
// ---------------------------------------------------------------------------
const axiosInstance = axios.create({
    timeout: 15000,
    maxRedirects: 10,
    httpAgent,
    httpsAgent,
    headers: {
        'User-Agent'              : 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
        'Accept'                  : 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8',
        'Accept-Language'         : 'en-US,en;q=0.9',
        'Accept-Encoding'         : 'gzip, deflate, br',
        'Cache-Control'           : 'no-cache',
        'Upgrade-Insecure-Requests': '1',
        'Sec-Fetch-Dest'          : 'document',
        'Sec-Fetch-Mode'          : 'navigate',
        'Sec-Fetch-Site'          : 'same-origin',
        'Sec-Fetch-User'          : '?1',
        'sec-ch-ua'               : '"Chromium";v="124", "Google Chrome";v="124", "Not-A.Brand";v="99"',
        'sec-ch-ua-mobile'        : '?0',
        'sec-ch-ua-platform'      : '"Windows"',
        'DNT'                     : '1',
        'Connection'              : 'keep-alive',
    },
    validateStatus: s => s < 500,
});

// ---------------------------------------------------------------------------
// In-memory TTL Cache
// — Always active regardless of DISABLE_CACHE env var.
// — Disk/Redis cache is for cross-process persistence; this is per-process.
// — TTLs are intentionally conservative so stale links don't accumulate.
// ---------------------------------------------------------------------------
class MemoryCache {
    constructor() { this._store = new Map(); }

    set(key, value, ttlMs) {
        this._store.set(key, { value, exp: Date.now() + ttlMs });
    }

    get(key) {
        const entry = this._store.get(key);
        if (!entry) return undefined;
        if (Date.now() > entry.exp) { this._store.delete(key); return undefined; }
        return entry.value;
    }

    has(key) { return this.get(key) !== undefined; }

    // Prune expired entries (called opportunistically)
    prune() {
        const now = Date.now();
        for (const [k, v] of this._store)
            if (now > v.exp) this._store.delete(k);
    }
}

const memCache = new MemoryCache();

// Prune stale entries every 5 minutes
setInterval(() => memCache.prune(), 5 * 60 * 1000).unref();

// Cache TTLs
const TTL = {
    TMDB      : 24 * 60 * 60 * 1000,  // 24h  — TMDB metadata rarely changes
    SEARCH    : 12 * 60 * 60 * 1000,  // 12h  — search page URL
    PAGE      : 60 * 60 * 1000,       //  1h  — full movie/show page HTML
    REDIRECT  :  4 * 60 * 60 * 1000,  //  4h  — redirect decoding result
    HUBCLOUD  : 30 * 60 * 1000,       // 30m  — HubCloud stream links (short-lived signed URLs)
};

// ---------------------------------------------------------------------------
// In-flight deduplication
// — If two concurrent requests hit the same URL at the same time,
//   only ONE real HTTP fetch is made; both callers await the same promise.
// ---------------------------------------------------------------------------
const inFlight = new Map();

function dedupFetch(key, fetcher) {
    if (inFlight.has(key)) return inFlight.get(key);
    const p = fetcher().finally(() => inFlight.delete(key));
    inFlight.set(key, p);
    return p;
}

// ---------------------------------------------------------------------------
// Core fetchText
// — Direct for 4khdhub.fans (not IP-blocked)
// — Routes through ScraperAPI proxy only for PROXY_DOMAINS (hubcloud.cx etc.)
// ---------------------------------------------------------------------------
function needsProxy(url) {
    try {
        const host = new URL(url).hostname;
        return PROXY_DOMAINS.has(host);
    } catch { return false; }
}

async function fetchText(url, extraHeaders = {}) {
    const cacheKey = `html:${url}`;
    const cached = memCache.get(cacheKey);
    if (cached !== undefined) {
        log(`Cache HIT (html): ${url}`);
        return cached;
    }

    return dedupFetch(cacheKey, async () => {
        const headers = { ...extraHeaders };
        const useProxy = needsProxy(url) && SCRAPER_API_KEY;

        let result = null;

        if (useProxy) {
            // Route through ScraperAPI residential proxy — skips datacenter IP ban
            const proxyUrl = `http://api.scraperapi.com?api_key=${SCRAPER_API_KEY}&url=${encodeURIComponent(url)}&render=false`;
            log(`Proxy fetch: ${url}`);
            try {
                const res = await axiosInstance.get(proxyUrl, { headers, timeout: 30000 });
                result = typeof res.data === 'string' ? res.data : null;
            } catch (e) {
                console.error(`[4KHDHub] Proxy fetch failed for ${url}: ${e.message}`);
            }
        } else {
            // Direct fetch for trusted domains
            try {
                const res = await axiosInstance.get(url, { headers });
                if (res.status === 403 || res.status === 401) {
                    console.warn(`[4KHDHub] Blocked (${res.status}) for ${url}${needsProxy(url) && !SCRAPER_API_KEY ? ' — set SCRAPER_API_KEY to fix on hosted deployments' : ''}`);
                    result = null;
                } else {
                    result = typeof res.data === 'string' ? res.data : null;
                }
            } catch (e) {
                console.error(`[4KHDHub] Fetch failed for ${url}: ${e.message}`);
                result = null;
            }
        }

        // Only cache successful responses
        if (result !== null) {
            memCache.set(cacheKey, result, TTL.PAGE);
        }
        return result;
    });
}

// ---------------------------------------------------------------------------
// atob polyfill
// ---------------------------------------------------------------------------
const atob = str => Buffer.from(str, 'base64').toString('binary');

// ---------------------------------------------------------------------------
// TMDB — accepts externally-provided details to skip the API round-trip
// ---------------------------------------------------------------------------
async function getTmdbDetails(tmdbId, type) {
    const cacheKey = `tmdb:${type}:${tmdbId}`;
    const cached = memCache.get(cacheKey);
    if (cached) return cached;

    const isSeries = type === 'series' || type === 'tv';
    const url = `https://api.themoviedb.org/3/${isSeries ? 'tv' : 'movie'}/${tmdbId}?api_key=${TMDB_API_KEY}`;
    log(`TMDB fetch: ${url}`);

    try {
        const res = await axiosInstance.get(url);
        const data = res.data;
        const result = isSeries
            ? { title: data.name,  year: data.first_air_date ? +data.first_air_date.slice(0, 4) : 0 }
            : { title: data.title, year: data.release_date   ? +data.release_date.slice(0, 4)   : 0 };
        memCache.set(cacheKey, result, TTL.TMDB);
        return result;
    } catch (e) {
        console.error(`[4KHDHub] TMDB fetch failed: ${e.message}`);
        return null;
    }
}

// ---------------------------------------------------------------------------
// fetchPageUrl — find the 4KHDHub show/movie page URL
// ---------------------------------------------------------------------------
async function fetchPageUrl(name, year, isSeries) {
    const cacheKey = `search:${name.toLowerCase().replace(/\W+/g, '_')}:${year}`;
    const cached = memCache.get(cacheKey);
    if (cached !== undefined) {
        log(`Cache HIT (search): ${name}`);
        return cached;
    }

    const searchUrl = `${BASE_URL}/?s=${encodeURIComponent(`${name} ${year}`)}`;
    const html = await fetchText(searchUrl);
    if (!html) return null;

    const $ = cheerio.load(html);
    const targetType = isSeries ? 'Series' : 'Movies';
    const nameLower = name.toLowerCase();

    let result = null;
    // Single-pass: collect all movie cards, filter & rank in one go
    const cards = [];
    $('.movie-card').each((_i, el) => {
        const $el = $(el);

        // Must match content type
        if (!$el.find(`.movie-card-format:contains("${targetType}")`).length) return;

        // Must match year (±1)
        const cardYear = parseInt($el.find('.movie-card-meta').text());
        if (isNaN(cardYear) || Math.abs(cardYear - year) > 1) return;

        // Title similarity check
        const cardTitle = $el.find('.movie-card-title').text().replace(/\[.*?]/g, '').trim();
        const dist = levenshtein.get(cardTitle.toLowerCase(), nameLower);
        if (dist >= 5) return;

        let href = $el.attr('href') || '';
        if (href && !href.startsWith('http')) href = BASE_URL + (href.startsWith('/') ? '' : '/') + href;
        if (href) cards.push({ href, dist });
    });

    // Pick best match (lowest edit distance)
    if (cards.length > 0) {
        cards.sort((a, b) => a.dist - b.dist);
        result = cards[0].href;
    }

    memCache.set(cacheKey, result, TTL.SEARCH);
    return result;
}

// ---------------------------------------------------------------------------
// resolveRedirectUrl — decode the obfuscated redirect chain
// ---------------------------------------------------------------------------
async function resolveRedirectUrl(redirectUrl) {
    const cacheKey = `redirect:${redirectUrl}`;
    const cached = memCache.get(cacheKey);
    if (cached !== undefined) {
        log(`Cache HIT (redirect): ${redirectUrl}`);
        return cached;
    }

    const html = await fetchText(redirectUrl);
    if (!html) return redirectUrl;

    try {
        const m = RE_REDIRECT_DATA.exec(html);
        if (!m) return redirectUrl;

        const decoded = JSON.parse(atob(rot13Cipher(atob(atob(m[1])))));
        if (decoded?.o) {
            const resolved = atob(decoded.o);
            memCache.set(cacheKey, resolved, TTL.REDIRECT);
            return resolved;
        }
    } catch (e) {
        logWarn(`Redirect decode error for ${redirectUrl}: ${e.message}`);
    }
    return redirectUrl;
}

// ---------------------------------------------------------------------------
// extractSourceResults — sync DOM extraction; resolves redirect URL async
// ---------------------------------------------------------------------------
async function extractSourceResults($, el) {
    const $el   = $(el);
    const html  = $el.html() || '';
    const title = $el.find('.file-title, .episode-file-title').text().trim();

    // Size
    const sizeMatch  = RE_SIZE.exec(html);
    // Height — prefer HTML badge, fallback to title text, fallback to '4K' keyword
    let heightMatch  = RE_HEIGHT.exec(html) || RE_HEIGHT.exec(title);
    let height = heightMatch ? parseInt(heightMatch[1]) : 0;
    if (!height && /4k/i.test(html + title)) height = 2160;

    const meta = {
        bytes : sizeMatch ? bytes.parse(sizeMatch[1]) : 0,
        height,
        title,
    };

    // Prefer HubCloud link
    const hubCloudAnchor = $el.find('a').filter((_i, a) => $(a).text().includes('HubCloud'));
    if (hubCloudAnchor.length) {
        const href    = hubCloudAnchor.attr('href');
        const resolved = href ? await resolveRedirectUrl(href) : null;
        return resolved ? { url: resolved, meta } : null;
    }

    // Fallback: HubDrive → inner HubCloud link
    const hubDriveAnchor = $el.find('a').filter((_i, a) => $(a).text().includes('HubDrive'));
    if (hubDriveAnchor.length) {
        const href    = hubDriveAnchor.attr('href');
        const driveUrl = href ? await resolveRedirectUrl(href) : null;
        if (driveUrl) {
            const driveHtml = await fetchText(driveUrl);
            if (driveHtml) {
                const $d     = cheerio.load(driveHtml);
                const inner  = $d('a:contains("HubCloud")').attr('href');
                if (inner) return { url: inner, meta };
            }
        }
    }

    return null;
}

// ---------------------------------------------------------------------------
// extractHubCloud — pull FSL + PixelServer download links from a HubCloud URL
// ---------------------------------------------------------------------------
async function extractHubCloud(hubCloudUrl, baseMeta) {
    if (!hubCloudUrl) return [];

    const cacheKey = `hubcloud:${hubCloudUrl}`;
    const cached = memCache.get(cacheKey);
    if (cached) {
        log(`Cache HIT (hubcloud): ${hubCloudUrl}`);
        return cached;
    }

    return dedupFetch(cacheKey, async () => {
        // Step 1: Fetch the HubCloud drive page
        // Use 4KHDHub as the Referer to simulate real navigation from the source page
        let origin = hubCloudUrl;
        try { const u = new URL(hubCloudUrl); origin = `${u.protocol}//${u.host}`; } catch {}

        const driveHtml = await fetchText(hubCloudUrl, {
            Referer         : `${BASE_URL}/`,
            Origin          : origin,
            'Sec-Fetch-Site': 'cross-site',
        });
        if (!driveHtml) return [];

        // Step 2: Extract the final links page URL from JS variable
        const urlMatch = RE_VAR_URL.exec(driveHtml);
        if (!urlMatch) {
            logWarn(`Could not find 'var url' in HubCloud page: ${hubCloudUrl}`);
            return [];
        }

        // Step 3: Fetch the actual download links page
        const linksPageUrl = urlMatch[1];
        const linksHtml = await fetchText(linksPageUrl, {
            Referer: hubCloudUrl,
            Origin : origin,
        });
        if (!linksHtml) return [];

        // Step 4: Single-pass parse — extract all links and the pxl override in one traversal
        const $ = cheerio.load(linksHtml);
        const sizeText  = $('#size').text();
        const titleText = $('title').text().trim();

        // Pre-scan scripts for JS-overridden PixelServer URL
        let jsPixelUrl = null;
        $('script').each((_i, s) => {
            if (jsPixelUrl) return; // already found
            const m = RE_PXL_VAR.exec($(s).html() || '');
            if (m) jsPixelUrl = m[1];
        });

        const currentMeta = {
            ...baseMeta,
            bytes : bytes.parse(sizeText) || baseMeta.bytes,
            title : titleText || baseMeta.title,
        };
        log(`Extracted meta: ${JSON.stringify(currentMeta)}`);

        const results = [];
        const seenUrls = new Set(); // de-duplicate identical links on the same page

        $('a').each((_i, el) => {
            const $a  = $(el);
            const text = $a.text().trim();
            let href   = $a.attr('href');
            if (!href) return;

            let source = null;
            if (text.includes('FSL') || text.includes('Download File')) {
                source = 'FSL';
            } else if (
                text.includes('PixelServer') ||
                text.includes('10Gbps') ||
                href.includes('pixel.hubcloud')
            ) {
                // Use JS-overridden URL if available (more up-to-date signed URL)
                if (jsPixelUrl) href = jsPixelUrl;
                href   = href.replace('/u/', '/api/file/');
                source = 'PixelServer';
            }

            if (source && href && !seenUrls.has(href)) {
                seenUrls.add(href);
                results.push({ source, url: href, meta: currentMeta });
            }
        });

        if (results.length) memCache.set(cacheKey, results, TTL.HUBCLOUD);
        return results;
    });
}

// ---------------------------------------------------------------------------
// buildStreamObject — deterministic stream object builder
// ---------------------------------------------------------------------------
const PLAYBACK_HEADERS = {
    Referer      : 'https://gamerxyt.com/',
    'User-Agent' : 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
};

function buildStreamName(source, meta) {
    const q   = meta.height === 2160 ? '4K' : meta.height ? `${meta.height}p` : '';
    const tag = source === 'PixelServer' ? 'PIX' : source === 'FSL' ? 'FSL' : source;

    // Deduplicated codec tags from title (Set prevents repeats)
    const t = meta.title || '';
    const codecs = new Set();
    if (/\bDV\b/i.test(t))     codecs.add('DV');
    if (/\bHDR\b/i.test(t))    codecs.add('HDR');
    if (/WEB[-.]DL/i.test(t))  codecs.add('WEB');
    if (/BluRay|BDRip/i.test(t)) codecs.add('BD');
    if (/REMUX/i.test(t))      codecs.add('REMUX');
    if (/AV1\b/i.test(t))      codecs.add('AV1');

    const codecStr = codecs.size ? ' ' + [...codecs].join(' | ') : '';
    return `4KHDHub [${tag}] [${q || '?'}]${codecStr}`;
}

function buildStream(link, sourceMeta) {
    return {
        name : buildStreamName(link.source, link.meta),
        title: `${link.meta.title}\n${bytes.format(link.meta.bytes || 0)}`,
        url  : link.url,
        quality: sourceMeta.height ? `${sourceMeta.height}p` : undefined,
        behaviorHints: {
            bingeGroup  : `4khdhub-${link.source}`,
            notWebReady : true,
            headers     : PLAYBACK_HEADERS,
            proxyHeaders: { request: PLAYBACK_HEADERS },
        },
    };
}

// ---------------------------------------------------------------------------
// get4KHDHubStreams — main entry point
//
// Accepts optional `externalTmdbDetails` to skip the duplicate TMDB API call
// when addon.js has already fetched it (saves ~300ms on every request).
// ---------------------------------------------------------------------------
async function get4KHDHubStreams(tmdbId, type, season = null, episode = null, externalTmdbDetails = null) {
    // ── 1. TMDB metadata ──────────────────────────────────────────────────
    const tmdbDetails = externalTmdbDetails || await getTmdbDetails(tmdbId, type);
    if (!tmdbDetails) return [];

    const { title, year } = tmdbDetails;
    log(`Search: "${title}" (${year})`);

    // ── 2. Find show/movie page ───────────────────────────────────────────
    const isSeries = type === 'series' || type === 'tv';
    const pageUrl  = await fetchPageUrl(title, year, isSeries);
    if (!pageUrl) { log('Page not found'); return []; }
    log(`Found page: ${pageUrl}`);

    // ── 3. Fetch & parse page ─────────────────────────────────────────────
    const html = await fetchText(pageUrl);
    if (!html) return [];
    const $ = cheerio.load(html);

    // ── 4. Collect items to process ───────────────────────────────────────
    let itemsToProcess = [];

    if (isSeries && season && episode) {
        const seasonStr  = `S${String(season).padStart(2, '0')}`;
        const episodeStr = `Episode-${String(episode).padStart(2, '0')}`;

        $('.episode-item').each((_i, el) => {
            if (!$('.episode-title', el).text().includes(seasonStr)) return;
            $('.episode-download-item', el)
                .filter((_j, item) => $(item).text().includes(episodeStr))
                .each((_k, item) => itemsToProcess.push(item));
        });
    } else {
        $('.download-item').each((_i, el) => itemsToProcess.push(el));
    }

    log(`Processing ${itemsToProcess.length} items with concurrency cap ${HUBCLOUD_CONCURRENCY}`);
    if (!itemsToProcess.length) return [];

    // ── 5. Concurrent extraction (with concurrency cap) ───────────────────
    const streamArrays = await Promise.all(
        itemsToProcess.map(item =>
            limit(async () => {
                try {
                    const sourceResult = await extractSourceResults($, item);
                    if (!sourceResult?.url) return [];

                    log(`Extracting HubCloud: ${sourceResult.url}`);
                    const links = await extractHubCloud(sourceResult.url, sourceResult.meta);
                    return links.map(link => buildStream(link, sourceResult.meta));
                } catch (err) {
                    console.error(`[4KHDHub] Item processing failed: ${err.message}`);
                    return [];
                }
            })
        )
    );

    const streams = streamArrays.flat();
    console.log(`[4KHDHub] Successfully fetched ${streams.length} streams.`);
    return streams;
}

module.exports = { get4KHDHubStreams };