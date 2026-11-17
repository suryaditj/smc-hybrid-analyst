#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SMC HYBRID ANALYST - Telegram bot analisis XAUUSD & BTCUSD
==========================================================
* Data     : OHLC dari BiQuote (https://biquote.io/api, tanpa API key)
* Analisis : 100% Python (SNR, SND, FVG, BOS, CHOCH + price action)
* Antarmuka: Telegram Bot API (python-telegram-bot >= 20)
* Tanpa AI Vision / Groq / OpenAI / Twelve Data. Hanya butuh TELEGRAM_BOT_TOKEN.

Bukan nasihat keuangan. Sinyal adalah hasil pembacaan struktur harga otomatis.
"""

import asyncio
import html
import logging
import math
import os
import re
import sys
import threading
import time
from collections import namedtuple
from datetime import datetime, timedelta, timezone
from statistics import median

import requests

try:
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
    from telegram.constants import ParseMode
    from telegram.error import BadRequest
    from telegram.ext import (Application, ApplicationBuilder, CallbackQueryHandler,
                              CommandHandler, ContextTypes)
    TELEGRAM_OK = True
except ImportError:  # mesin analisis tetap bisa diimpor tanpa telegram
    TELEGRAM_OK = False

# =============================================================================
# KONFIGURASI
# =============================================================================
# Isi token di sini ATAU set environment variable TELEGRAM_BOT_TOKEN.
TELEGRAM_BOT_TOKEN = "TELEGRAM_BOT_TOKEN"

# Opsional: batasi pemakai (kosongkan = semua orang boleh). Contoh: {123456789}
ALLOWED_USER_IDS = set()

BIQUOTE_BASE = "https://biquote.io/api"
SYMBOLS = ["XAUUSD", "BTCUSD"]
LIMIT_NATIVE = 500          # jumlah candle yang diminta per request
LIMIT_H1_FALLBACK = 1000    # untuk agregasi H4/D1 dari H1
CACHE_TTL = 10              # detik; analisis ulang selalu melewati cache
MIN_CLOSED_CANDLES = 80
MIN_CLOSED_AGGREGATED = 30   # H4/D1 hasil agregasi H1 punya riwayat lebih pendek
MAX_ANALYSIS_CANDLES = 400
WIB = timezone(timedelta(hours=7))

# sec: durasi candle | native: nilai parameter interval BiQuote
# htf: timeframe konteks | swing: lebar fractal swing
TF_CONFIG = {
    "M1":  {"sec": 60,    "native": "1m",  "htf": "M5",  "swing": 3},
    "M5":  {"sec": 300,   "native": "5m",  "htf": "M15", "swing": 3},
    "M15": {"sec": 900,   "native": "15m", "htf": "H1",  "swing": 3},
    "M30": {"sec": 1800,  "native": "30m", "htf": "H1",  "swing": 3},
    "H1":  {"sec": 3600,  "native": "1h",  "htf": "H4",  "swing": 3},
    "H4":  {"sec": 14400, "native": "4h",  "htf": "D1",  "swing": 2},
    "D1":  {"sec": 86400, "native": "1d",  "htf": "H4",  "swing": 2},
}
TF_ORDER = ["M1", "M5", "M15", "M30", "H1", "H4", "D1"]

logging.basicConfig(format="%(asctime)s %(levelname)s %(name)s: %(message)s",
                    level=logging.INFO)
logging.getLogger("httpx").setLevel(logging.WARNING)
logger = logging.getLogger("smc")

# =============================================================================
# DATA LAYER - BiQuote
# =============================================================================
Candle = namedtuple("Candle", "t o h l c")   # t = epoch detik (waktu open)


class DataError(Exception):
    def __init__(self, msg, status=None):
        super().__init__(msg)
        self.status = status


SESSION = requests.Session()
SESSION.headers.update({"User-Agent": "SMC-Hybrid-Analyst/1.0", "Accept": "application/json"})

_cache = {}
_cache_lock = threading.Lock()


def _http_get_json(url, params=None):
    last = "tidak diketahui"
    for attempt in range(3):
        try:
            r = SESSION.get(url, params=params, timeout=(5, 20))
        except requests.Timeout:
            last = "timeout"
        except requests.ConnectionError:
            last = "koneksi terputus"
        except requests.RequestException as e:
            last = "error jaringan: %s" % type(e).__name__
        else:
            if r.status_code == 200:
                try:
                    return r.json()
                except ValueError:
                    raise DataError("respons BiQuote bukan JSON yang valid")
            if r.status_code in (400, 404, 422):
                raise DataError("HTTP %d dari BiQuote" % r.status_code, status=r.status_code)
            last = "HTTP %d" % r.status_code
            if r.status_code not in (429, 500, 502, 503, 504):
                raise DataError("HTTP %d dari BiQuote" % r.status_code, status=r.status_code)
        if attempt < 2:
            time.sleep(1.2 * (attempt + 1))
    raise DataError("BiQuote tidak dapat dijangkau (%s)" % last)


def _parse_time(x):
    """Epoch detik/milidetik atau string ISO -> epoch detik (float), None bila gagal."""
    if isinstance(x, bool):
        return None
    if isinstance(x, (int, float)):
        v = float(x)
    elif isinstance(x, str):
        s = x.strip()
        try:
            v = float(s)
        except ValueError:
            s2 = s.replace("Z", "+00:00").replace(" ", "T", 1)
            try:
                d = datetime.fromisoformat(s2)
            except ValueError:
                try:
                    d = datetime.strptime(s[:19], "%Y-%m-%dT%H:%M:%S")
                except ValueError:
                    return None
            if d.tzinfo is None:
                d = d.replace(tzinfo=timezone.utc)
            return d.timestamp()
    else:
        return None
    if v > 1e12:
        v /= 1000.0
    if v < 1e9:
        return None
    return v


def _extract_rows(data):
    if isinstance(data, list):
        return data
    if isinstance(data, dict):
        for k in ("bars", "candles", "data", "ohlc", "result", "items"):
            v = data.get(k)
            if isinstance(v, list):
                return v
            if isinstance(v, dict):
                sub = _extract_rows(v)
                if sub is not None:
                    return sub
    return None


_KEYS_T = ("time", "t", "timestamp", "ts", "opentime", "open_time", "datetime", "date", "d")
_KEYS_O = ("open", "o")
_KEYS_H = ("high", "h")
_KEYS_L = ("low", "l")
_KEYS_C = ("close", "c")


def _pick(d, keys):
    for k in keys:
        if k in d and d[k] is not None:
            return d[k]
    return None


def _to_float(x):
    try:
        v = float(x)
    except (TypeError, ValueError):
        return None
    return v if math.isfinite(v) else None


def parse_rows(rows):
    """Ubah baris respons menjadi daftar Candle mentah. Baris rusak dihitung."""
    out, bad = [], 0
    for r in rows:
        t = o = h = l = c = None
        if isinstance(r, dict):
            low = {str(k).lower(): v for k, v in r.items()}
            t = _parse_time(_pick(low, _KEYS_T))
            o, h, l, c = (_to_float(_pick(low, k)) for k in (_KEYS_O, _KEYS_H, _KEYS_L, _KEYS_C))
        elif isinstance(r, (list, tuple)) and len(r) >= 5:
            t = _parse_time(r[0])
            o, h, l, c = (_to_float(v) for v in r[1:5])
        if t is None or None in (o, h, l, c) or min(o, h, l, c) <= 0:
            bad += 1
            continue
        out.append(Candle(int(t), o, h, l, c))
    if rows and bad > 0.3 * len(rows):
        raise DataError("format candle BiQuote tidak dikenali (%d/%d baris tidak valid)" % (bad, len(rows)))
    return out


def clean_candles(cs):
    """Urutkan, buang duplikat (ambil yang terakhir), perbaiki OHLC, buang candle kosong."""
    by_t = {}
    for c in cs:
        by_t[c.t] = c
    res = []
    for t in sorted(by_t):
        c = by_t[t]
        h = max(c.h, c.o, c.c, c.l)
        l = min(c.l, c.o, c.c, c.h)
        if h == l:      # candle datar tanpa range = tidak ada informasi
            continue
        res.append(Candle(c.t, c.o, h, l, c.c))
    return res


def _fetch_native(symbol, interval_str, limit):
    url = "%s/%s/ohlc" % (BIQUOTE_BASE, symbol)
    data = _http_get_json(url, {"interval": interval_str, "limit": limit})
    rows = _extract_rows(data)
    if rows is None:
        raise DataError("struktur respons OHLC BiQuote tidak dikenali")
    cs = clean_candles(parse_rows(rows))
    if not cs:
        raise DataError("BiQuote tidak mengirim candle untuk %s interval %s" % (symbol, interval_str))
    return cs


def _check_spacing(cs, sec):
    if len(cs) < 10:
        return
    deltas = [b.t - a.t for a, b in zip(cs, cs[1:])]
    med = median(deltas)
    if not (0.9 * sec <= med <= 1.1 * sec):
        raise DataError("jarak candle (%ds) tidak sesuai timeframe (%ds)" % (med, sec))


def _aggregate(cs, sec):
    buckets = {}
    for c in cs:
        buckets.setdefault((c.t // sec) * sec, []).append(c)
    keys = sorted(buckets)
    out = []
    for k in keys:
        g = buckets[k]
        out.append(Candle(k, g[0].o, max(x.h for x in g), min(x.l for x in g), g[-1].c))
    return out[1:] if len(out) > 1 else out   # bucket pertama terpotong jendela data


def _fetch_uncached(symbol, tf):
    cfg = TF_CONFIG[tf]
    sec = cfg["sec"]
    warnings = []
    min_needed = MIN_CLOSED_CANDLES
    try:
        cs = _fetch_native(symbol, cfg["native"], LIMIT_NATIVE)
        _check_spacing(cs, sec)
        source = "BiQuote %s" % cfg["native"]
    except DataError as e:
        if tf not in ("H4", "D1"):
            raise
        logger.warning("interval native %s gagal (%s); agregasi dari H1", cfg["native"], e)
        try:
            base = _fetch_native(symbol, TF_CONFIG["H1"]["native"], LIMIT_H1_FALLBACK)
        except DataError:
            base = _fetch_native(symbol, TF_CONFIG["H1"]["native"], LIMIT_NATIVE)
        cs = _aggregate(base, sec)
        source = "agregasi dari H1 (interval %s tidak tersedia)" % cfg["native"]
        warnings.append("%s dibentuk dari candle H1 (batas hari/4 jam = UTC, bisa berbeda dari broker)." % tf)
        min_needed = MIN_CLOSED_AGGREGATED

    now = time.time()
    skew = cs[-1].t - now
    if skew > 120:   # waktu candle di masa depan -> kemungkinan memakai jam server
        off = int(round(skew / 1800.0)) * 1800
        if 0 < off <= 14 * 3600:
            cs = [Candle(c.t - off, c.o, c.h, c.l, c.c) for c in cs]
            warnings.append("Timestamp BiQuote tampak memakai zona waktu server (+%.1f jam); dikoreksi otomatis." % (off / 3600.0))
        else:
            raise DataError("timestamp candle terakhir berada di masa depan (%.0f detik)" % skew)

    forming = None
    if now < cs[-1].t + sec:
        forming = cs[-1]
        cs = cs[:-1]
    if len(cs) < min_needed:
        raise DataError("candle tertutup hanya %d (minimal %d) untuk %s %s" % (len(cs), min_needed, symbol, tf))
    if len(cs) < 100:
        warnings.append("Riwayat candle pendek (%d); struktur & zona kurang andal." % len(cs))

    ref_open = forming.t if forming else cs[-1].t
    age = now - ref_open
    stale = (forming is None) and (age > 2 * sec + max(120, 0.1 * sec))
    if stale:
        warnings.append("Data tidak segar: candle terakhir dibuka %s yang lalu. Market mungkin tutup atau feed tertunda; jangan eksekusi." % fmt_dur(age))
    return {"symbol": symbol, "tf": tf, "closed": cs, "forming": forming, "source": source,
            "warnings": warnings, "stale": stale, "fetched": now, "age": age}


def fetch_candles(symbol, tf, force=False):
    key = (symbol, tf)
    if not force:
        with _cache_lock:
            hit = _cache.get(key)
        if hit and time.time() - hit[0] < CACHE_TTL:
            return hit[1]
    res = _fetch_uncached(symbol, tf)
    with _cache_lock:
        _cache[key] = (time.time(), res)
    return res


def fetch_price(symbol, ref_price, atr):
    """Harga terkini dari endpoint tick BiQuote. Mengembalikan (harga, info) atau (None, alasan)."""
    try:
        d = _http_get_json("%s/%s" % (BIQUOTE_BASE, symbol))
    except DataError as e:
        return None, str(e)
    if isinstance(d, list) and d:
        d = d[0]
    if not isinstance(d, dict):
        return None, "format tick tidak dikenali"
    low = {str(k).lower(): v for k, v in d.items()}
    mid = _to_float(low.get("mid"))
    if mid is None:
        b, a = _to_float(low.get("bid")), _to_float(low.get("ask"))
        if b and a:
            mid = (b + a) / 2.0
    if mid is None or mid <= 0:
        return None, "tick tanpa harga"
    if abs(mid - ref_price) > max(8 * atr, 0.03 * ref_price):
        return None, "harga tick menyimpang jauh dari candle"
    note = ""
    if low.get("marketopen") is False:
        note = "BiQuote menandai market tutup."
    return mid, note


# =============================================================================
# MESIN SMC
# =============================================================================
def clip(x, lo=0.0, hi=1.0):
    return max(lo, min(hi, x))


def atr_series(cs, n=14):
    """Rata-rata true range (ukuran volatilitas untuk toleransi zona, bukan sinyal)."""
    trs, prev = [], None
    for c in cs:
        tr = (c.h - c.l) if prev is None else max(c.h - c.l, abs(c.h - prev.c), abs(c.l - prev.c))
        trs.append(tr)
        prev = c
    out = []
    run = 0.0
    for i, tr in enumerate(trs):
        run += tr
        if i >= n:
            run -= trs[i - n]
            out.append(run / n)
        else:
            out.append(run / (i + 1))
    return out


class Swing(object):
    __slots__ = ("i", "kind", "p", "broken", "swept")

    def __init__(self, i, kind, p):
        self.i, self.kind, self.p = i, kind, p
        self.broken = False
        self.swept = False


Event = namedtuple("Event", "kind dirn i level ref_i")     # kind BOS/CHOCH, dirn bull/bear
Sweep = namedtuple("Sweep", "dirn i level")                # bull = low disapu, bear = high disapu


def find_swings(cs, n):
    sw = []
    for i in range(n, len(cs) - n):
        hi, lo = cs[i].h, cs[i].l
        if all(hi > cs[j].h for j in range(i - n, i)) and all(hi >= cs[j].h for j in range(i + 1, i + n + 1)):
            sw.append(Swing(i, "H", hi))
        if all(lo < cs[j].l for j in range(i - n, i)) and all(lo <= cs[j].l for j in range(i + 1, i + n + 1)):
            sw.append(Swing(i, "L", lo))
    return sw


def analyze_structure(cs, atr, n):
    """BOS / CHOCH berbasis candle close + deteksi sweep (false breakout)."""
    swings = find_swings(cs, n)
    conf = {}
    for s in swings:
        conf.setdefault(s.i + n, []).append(s)
    events, sweeps = [], []
    trend = 0
    last_h = last_l = None
    for i, c in enumerate(cs):
        for s in conf.get(i, []):
            if s.kind == "H":
                last_h = s
            else:
                last_l = s
        a = atr[i]
        body = abs(c.c - c.o)
        if last_h is not None and not last_h.broken:
            ext = c.c - last_h.p
            if ext >= 0.1 * a:
                is_choch = trend < 0
                if (not is_choch) or ext >= 0.25 * a or body >= 0.6 * a:
                    events.append(Event("CHOCH" if is_choch else "BOS", "bull", i, last_h.p, last_h.i))
                    last_h.broken = True
                    trend = 1
            elif c.h > last_h.p and c.c < last_h.p and not last_h.swept:
                last_h.swept = True
                sweeps.append(Sweep("bear", i, last_h.p))
        if last_l is not None and not last_l.broken:
            ext = last_l.p - c.c
            if ext >= 0.1 * a:
                is_choch = trend > 0
                if (not is_choch) or ext >= 0.25 * a or body >= 0.6 * a:
                    events.append(Event("CHOCH" if is_choch else "BOS", "bear", i, last_l.p, last_l.i))
                    last_l.broken = True
                    trend = -1
            elif c.l < last_l.p and c.c > last_l.p and not last_l.swept:
                last_l.swept = True
                sweeps.append(Sweep("bull", i, last_l.p))
    return {"swings": swings, "events": events, "sweeps": sweeps, "trend": trend}


def _visits(cs, start, low, high):
    """Kelompokkan candle (mulai index start) yang menyentuh zona menjadi kunjungan."""
    groups, cur = [], None
    for i in range(start, len(cs)):
        if cs[i].l <= high and cs[i].h >= low:
            if cur is None:
                cur = [i, i]
            else:
                cur[1] = i
        elif cur is not None:
            groups.append(tuple(cur))
            cur = None
    if cur is not None:
        groups.append(tuple(cur))
    return groups


def build_snr(cs, swings, atr_now, price):
    if not swings:
        return []
    tol = 0.4 * atr_now
    pts = sorted(((s.p, s.i) for s in swings))
    clusters, cur = [], [pts[0]]
    for p in pts[1:]:
        if p[0] - cur[0][0] <= tol:
            cur.append(p)
        else:
            clusters.append(cur)
            cur = [p]
    clusters.append(cur)
    zones = []
    n = len(cs)
    for cl in clusters:
        lo = min(p for p, _ in cl)
        hi = max(p for p, _ in cl)
        half = 0.15 * atr_now
        if hi - lo < 2 * half:
            mid0 = (hi + lo) / 2.0
            lo, hi = mid0 - half, mid0 + half
        mid = (lo + hi) / 2.0
        first_i = min(i for _, i in cl)
        touches = rejections = breaks = 0
        wicks = []
        last_touch = first_i
        for (a, b) in _visits(cs, first_i, lo, hi):
            before = cs[a - 1].c if a > 0 else None
            after = cs[b + 1].c if b + 1 < n else None
            touches += 1
            last_touch = b
            if before is None or after is None:
                continue
            sb, sa = before > mid, after > mid
            if sb == sa:
                rejections += 1
                best = 0.0
                for k in range(a, b + 1):
                    r = cs[k].h - cs[k].l
                    if r > 0:
                        w = (cs[k].h - max(cs[k].o, cs[k].c)) / r if sb else (min(cs[k].o, cs[k].c) - cs[k].l) / r
                        best = max(best, w)
                wicks.append(best)
            else:
                breaks += 1
        touches = max(touches, len(cl))
        avg_w = sum(wicks) / len(wicks) if wicks else 0.0
        st = 0.55 * min(rejections, 4) / 4.0 + 0.20 * min(touches, 5) / 5.0 + 0.25 * avg_w
        recency = 1.0 - 0.3 * clip((n - 1 - last_touch) / 250.0)
        st *= recency
        if breaks >= 2:
            st *= 0.6
        zones.append({"low": lo, "high": hi, "mid": mid, "touches": touches, "rejections": rejections,
                      "breaks": breaks, "strength": clip(st),
                      "role": "support" if mid < price else "resistance"})
    return zones


def build_snd(cs, atr, events):
    zones = []
    n = len(cs)
    for i in range(2, n):
        c = cs[i]
        a = atr[i - 1]
        rng = c.h - c.l
        body = abs(c.c - c.o)
        if rng <= 0 or body < 1.3 * a or body / rng < 0.55:
            continue
        dirn = 1 if c.c > c.o else -1
        base = []
        j = i - 1
        while j >= max(0, i - 3) and (cs[j].h - cs[j].l) <= 0.9 * a:
            base.insert(0, j)
            j -= 1
        if not base:   # fallback: candle berlawanan arah terakhir (order-block style)
            for j in range(i - 1, max(-1, i - 4), -1):
                if (cs[j].c - cs[j].o) * dirn < 0:
                    base = [j]
                    break
        if not base:
            continue
        b_low = min(cs[j].l for j in base)
        b_high = max(cs[j].h for j in base)
        if dirn > 0 and c.c <= b_high:
            continue
        if dirn < 0 and c.c >= b_low:
            continue
        low, high = b_low, b_high
        if high - low > 1.2 * a:    # basis terlalu tebal -> pakai body
            if dirn > 0:
                high = max(max(cs[j].o, cs[j].c) for j in base)
            else:
                low = min(min(cs[j].o, cs[j].c) for j in base)
        if high - low <= 0:
            continue
        disp = clip((body / a) / 2.5)
        imb = i + 1 < n and ((dirn > 0 and cs[i + 1].l > cs[i - 1].h) or (dirn < 0 and cs[i + 1].h < cs[i - 1].l))
        broken = False
        for k in range(i + 1, n):
            if dirn > 0 and cs[k].c < low - 0.1 * a:
                broken = True
                break
            if dirn < 0 and cs[k].c > high + 0.1 * a:
                broken = True
                break
        if broken:
            continue
        visits = len(_visits(cs, i + 1, low, high))
        if visits > 2:
            continue
        fresh_f = (1.0, 0.7, 0.4)[visits]
        tied = any(e.dirn == ("bull" if dirn > 0 else "bear") and i <= e.i <= i + 3 for e in events)
        st = 0.5 * disp + 0.2 * (1.0 if imb else 0.0) + 0.3 * fresh_f + (0.1 if tied else 0.0)
        zones.append({"kind": "demand" if dirn > 0 else "supply", "low": low, "high": high,
                      "origin": low if dirn > 0 else high, "strength": clip(st), "visits": visits,
                      "status": ("fresh", "retest 1x", "retest 2x")[visits], "i": i, "imb": imb})
    # buang zona saling menumpuk (simpan yang terkuat)
    zones.sort(key=lambda z: -z["strength"])
    kept = []
    for z in zones:
        dup = False
        for k in kept:
            if k["kind"] == z["kind"] and z["low"] <= k["high"] and k["low"] <= z["high"]:
                ov = min(z["high"], k["high"]) - max(z["low"], k["low"])
                if ov >= 0.5 * min(z["high"] - z["low"], k["high"] - k["low"]):
                    dup = True
                    break
        if not dup:
            kept.append(z)
    return kept


def build_fvg(cs, atr):
    out = []
    n = len(cs)
    for k in range(2, n):
        a = atr[k]
        c0, c1, c2 = cs[k - 2], cs[k - 1], cs[k]
        if c2.l > c0.h:
            bull, lo, hi, origin = True, c0.h, c2.l, min(c0.l, c1.l)
        elif c2.h < c0.l:
            bull, lo, hi, origin = False, c2.h, c0.l, max(c0.h, c1.h)
        else:
            continue
        size0 = hi - lo
        if size0 < 0.12 * a:
            continue
        status, fill = "fresh", 0.0
        for m in range(k + 1, n):
            cm = cs[m]
            if bull:
                if cm.l <= lo:
                    status = "filled"
                    break
                if cm.l < hi:
                    hi = cm.l
                    status = "touched"
                    fill = (c2.l - hi) / size0
            else:
                if cm.h >= hi:
                    status = "filled"
                    break
                if cm.h > lo:
                    lo = cm.h
                    status = "touched"
                    fill = (lo - c2.h) / size0
        if status == "filled" or (hi - lo) < 0.05 * a:
            continue
        age = n - 1 - k
        if age > 200:
            continue
        disp = clip(abs(c1.c - c1.o) / a / 1.5)
        st = (0.4 * disp + 0.3 * (1.0 if status == "fresh" else 0.6)
              + 0.15 * clip(size0 / a / 0.8) + 0.15 * (1.0 - age / 200.0))
        out.append({"kind": "bull" if bull else "bear", "low": lo, "high": hi, "origin": origin,
                    "strength": clip(st), "status": status, "fill": fill, "i": k})
    out.sort(key=lambda z: -z["i"])
    res = {"bull": [], "bear": []}
    for z in out:
        if len(res[z["kind"]]) < 8:
            res[z["kind"]].append(z)
    return res["bull"] + res["bear"]


def efficiency(cs, n=30):
    seg = cs[-n:]
    if len(seg) < 5:
        return 0.0
    path = sum(abs(b.c - a.c) for a, b in zip(seg, seg[1:]))
    return abs(seg[-1].c - seg[0].c) / path if path > 0 else 0.0


def _wick_lo(c):
    r = c.h - c.l
    return (min(c.o, c.c) - c.l) / r if r > 0 else 0.0


def _wick_hi(c):
    r = c.h - c.l
    return (c.h - max(c.o, c.c)) / r if r > 0 else 0.0


def pa_scores(cs, a):
    c1, c2, c3 = cs[-1], cs[-2], cs[-3]
    signed = sum(c.c - c.o for c in (c1, c2, c3)) / (3.0 * a)
    mom_b, mom_s = clip(signed), clip(-signed)
    rej_b = 1.0 if (_wick_lo(c1) >= 0.5 and c1.c >= c1.l + 0.5 * (c1.h - c1.l)) else (0.5 if _wick_lo(c1) >= 0.35 and c1.c > c1.o else 0.0)
    rej_s = 1.0 if (_wick_hi(c1) >= 0.5 and c1.c <= c1.l + 0.5 * (c1.h - c1.l)) else (0.5 if _wick_hi(c1) >= 0.35 and c1.c < c1.o else 0.0)
    eng_b = 1.0 if (c2.c < c2.o and c1.c > c1.o and c1.c > c2.o and c1.o <= c2.c) else 0.0
    eng_s = 1.0 if (c2.c > c2.o and c1.c < c1.o and c1.c < c2.o and c1.o >= c2.c) else 0.0
    imp_b = 1.0 if any((c.c - c.o) >= 1.3 * a for c in (c1, c2, c3)) else 0.0
    imp_s = 1.0 if any((c.o - c.c) >= 1.3 * a for c in (c1, c2, c3)) else 0.0
    return {
        "BUY": (clip(0.4 * mom_b + 0.25 * rej_b + 0.2 * eng_b + 0.15 * imp_b), rej_b, eng_b, imp_b),
        "SELL": (clip(0.4 * mom_s + 0.25 * rej_s + 0.2 * eng_s + 0.15 * imp_s), rej_s, eng_s, imp_s),
    }


def prox(dist):
    return 1.0 if dist <= 0 else max(0.0, 0.9 * (1.0 - dist / 2.5))


def zone_dist(d, z, price, a):
    """Jarak (satuan ATR) harga ke zona entry untuk arah d, None jika zona tidak relevan/rusak."""
    if d == "BUY":
        if z["low"] > price + 0.05 * a or price < z["low"] - 0.3 * a:
            return None
        return max(0.0, price - z["high"]) / a
    if z["high"] < price - 0.05 * a or price > z["high"] + 0.3 * a:
        return None
    return max(0.0, z["low"] - price) / a


def dynamic_weights(regime, last_event, age):
    w = {"struct": 30.0, "snr": 20.0, "snd": 20.0, "fvg": 20.0, "pa": 10.0}
    if regime == "RANGING":
        w["snr"] += 6; w["snd"] += 3; w["struct"] -= 7; w["fvg"] -= 2
    elif last_event is not None and last_event.kind == "CHOCH" and age <= 15:
        w["struct"] += 3; w["snd"] += 3; w["snr"] -= 3; w["fvg"] -= 3
    elif regime == "TRENDING":
        w["struct"] += 4; w["fvg"] += 3; w["snr"] -= 5; w["snd"] -= 2
    return w


def direction_components(d, ctx):
    cs, a, price = ctx["cs"], ctx["atr"], ctx["price"]
    st = ctx["structure"]
    events, sweeps = st["events"], st["sweeps"]
    n = len(cs)
    want = "bull" if d == "BUY" else "bear"
    info = {}
    last = events[-1] if events else None
    sup_sweep = [s for s in sweeps if s.dirn == want and n - 1 - s.i <= 12]
    if last is not None and last.dirn == want:
        age = n - 1 - last.i
        fac = max(0.35, 1.0 - age / 45.0)
        s_c = (1.0 if last.kind == "BOS" else 0.9) * fac
        if len(events) >= 2 and events[-2].dirn == want:
            s_c += 0.05
        info["event"] = (last, age)
    else:
        s_c = 0.08
    if sup_sweep:
        s_c += 0.15
        info["sweep"] = sup_sweep[-1]
    s_c = clip(s_c)

    def best(zs, key_ok):
        b, bd = 0.0, None
        for z in zs:
            if not key_ok(z):
                continue
            dist = zone_dist(d, z, price, a)
            if dist is None:
                continue
            v = z["strength"] * prox(dist)
            if v > b:
                b, bd = v, (z, dist)
        return b, bd

    snr_c, snr_z = best(ctx["snr"], lambda z: z["role"] == ("support" if d == "BUY" else "resistance") or zone_dist(d, z, price, a) == 0.0)
    snd_c, snd_z = best(ctx["snd"], lambda z: z["kind"] == ("demand" if d == "BUY" else "supply"))
    fvg_c, fvg_z = best(ctx["fvg"], lambda z: z["kind"] == ("bull" if d == "BUY" else "bear"))
    pa_c, rej, eng, imp = ctx["pa"][d]
    info.update({"snr": snr_z, "snd": snd_z, "fvg": fvg_z, "rej": rej, "eng": eng, "imp": imp})
    comps = {"struct": s_c, "snr": snr_c, "snd": snd_c, "fvg": fvg_c, "pa": pa_c}
    return comps, info


def collect_targets(d, entry, a, ctx):
    t = []
    price_lvls = []
    if d == "BUY":
        for s in ctx["structure"]["swings"]:
            if s.kind == "H" and not s.broken and not s.swept and s.p > entry:
                price_lvls.append((s.p, "swing high"))
        for z in ctx["snr"]:
            if z["low"] > entry and z["role"] == "resistance":
                price_lvls.append((z["low"], "resistance"))
        for z in ctx["snd"]:
            if z["kind"] == "supply" and z["low"] > entry:
                price_lvls.append((z["low"], "zona supply"))
        for p, lab in ctx.get("htf_levels", []):
            if lab == "H" and p > entry:
                price_lvls.append((p, "swing high HTF"))
        out = sorted(((p - 0.1 * a, lab, p) for p, lab in price_lvls), key=lambda x: x[0])
    else:
        for s in ctx["structure"]["swings"]:
            if s.kind == "L" and not s.broken and not s.swept and s.p < entry:
                price_lvls.append((s.p, "swing low"))
        for z in ctx["snr"]:
            if z["high"] < entry and z["role"] == "support":
                price_lvls.append((z["high"], "support"))
        for z in ctx["snd"]:
            if z["kind"] == "demand" and z["high"] < entry:
                price_lvls.append((z["high"], "zona demand"))
        for p, lab in ctx.get("htf_levels", []):
            if lab == "L" and p < entry:
                price_lvls.append((p, "swing low HTF"))
        out = sorted(((p + 0.1 * a, lab, p) for p, lab in price_lvls), key=lambda x: -x[0])
    return out


def pick_entry(d, ctx):
    a, price = ctx["atr"], ctx["price"]
    cands = []
    for z in ctx["snd"]:
        if z["kind"] == ("demand" if d == "BUY" else "supply"):
            cands.append({"src": "SND", "low": z["low"], "high": z["high"], "origin": z["origin"],
                          "strength": z["strength"], "status": z["status"]})
    for z in ctx["fvg"]:
        if z["kind"] == ("bull" if d == "BUY" else "bear"):
            cands.append({"src": "FVG", "low": z["low"], "high": z["high"], "origin": z["origin"],
                          "strength": z["strength"], "status": z["status"]})
    for z in ctx["snr"]:
        if z["role"] == ("support" if d == "BUY" else "resistance") or zone_dist(d, z, price, a) == 0.0:
            cands.append({"src": "SNR", "low": z["low"], "high": z["high"],
                          "origin": z["low"] if d == "BUY" else z["high"],
                          "strength": z["strength"], "status": "%dx reaksi" % z["rejections"]})
    valid = []
    for c in cands:
        dist = zone_dist(d, c, price, a)
        if dist is not None:
            c["dist"] = dist
            valid.append(c)
    if not valid:
        return None
    near = [c for c in valid if c["dist"] <= 2.5]
    pool = near if near else [c for c in valid if c["dist"] <= 8.0]
    if not pool:
        return None
    pool.sort(key=lambda c: -(c["strength"] * (1.0 - 0.25 * c["dist"] / 2.5)))
    prim = pool[0]
    lo, hi = prim["low"], prim["high"]
    srcs = [prim["src"]]
    origin = prim["origin"]
    for c in pool[1:]:
        if c["low"] <= hi and lo <= c["high"]:
            nlo, nhi = max(lo, c["low"]), min(hi, c["high"])
            if nhi - nlo >= 0.12 * a:
                lo, hi = nlo, nhi
            if c["src"] not in srcs:
                srcs.append(c["src"])
            origin = min(origin, c["origin"]) if d == "BUY" else max(origin, c["origin"])
    return {"low": lo, "high": hi, "origin": origin, "srcs": srcs, "dist": prim["dist"],
            "late": not near, "status": prim["status"], "strength": prim["strength"]}


def build_trade(d, ctx, zone):
    a, price = ctx["atr"], ctx["price"]
    buf = 0.25 * a
    if d == "BUY":
        ref = price if price <= zone["high"] else (zone["high"] + zone["low"]) / 2.0
        sl = zone["origin"] - buf
        risk = ref - sl
        if risk < 0.5 * a:
            sl = ref - 0.5 * a
            risk = 0.5 * a
        sign = 1
    else:
        ref = price if price >= zone["low"] else (zone["high"] + zone["low"]) / 2.0
        sl = zone["origin"] + buf
        risk = sl - ref
        if risk < 0.5 * a:
            sl = ref + 0.5 * a
            risk = 0.5 * a
        sign = -1
    if risk > 4.5 * a:
        return None, "stop loss struktural terlalu jauh (%.1f ATR) sehingga risiko tidak masuk akal" % (risk / a)
    targets = collect_targets(d, ref, a, ctx)
    cand = [t for t in targets if abs(t[0] - ref) >= 1.0 * risk]
    tp1_note = tp2_note = None
    if not targets:
        tp1 = ref + sign * 1.5 * risk
        tp1_note = "proyeksi 1:1.5 (tidak ada level struktural di depan)"
    elif not cand:
        return None, "target struktural terdekat kurang dari 1R dari entry (ruang gerak terbatas)"
    else:
        tp1 = cand[0][0]
        tp1_note = cand[0][1]
    rest = [t for t in cand if sign * (t[0] - tp1) >= 0.5 * a and abs(t[0] - ref) >= 1.6 * risk]
    if rest:
        tp2, tp2_note = rest[0][0], rest[0][1]
    else:
        tp2 = ref + sign * max(3.0 * risk, abs(tp1 - ref) + 1.0 * risk)
        tp2_note = "proyeksi (tidak ada level struktural lebih jauh)"
    tp3 = tp3_note = None
    if rest:   # TP3 hanya bila masih ada level struktural setelah TP2
        more = [t for t in cand if sign * (t[0] - tp2) >= 0.5 * a]
        if more:
            tp3, tp3_note = more[0][0], more[0][1]
    return {"entry_low": zone["low"], "entry_high": zone["high"], "ref": ref, "sl": sl, "tp1": tp1, "tp2": tp2,
            "tp3": tp3, "tp3_note": tp3_note,
            "tp1_note": tp1_note, "tp2_note": tp2_note, "risk": risk, "inv": zone["origin"],
            "rr1": abs(tp1 - ref) / risk, "rr2": abs(tp2 - ref) / risk}, None


def htf_summary(series):
    cs = series["closed"][-MAX_ANALYSIS_CANDLES:]
    n = TF_CONFIG[series["tf"]]["swing"]
    atr = atr_series(cs)
    st = analyze_structure(cs, atr, n)
    ev = st["events"][-1] if st["events"] else None
    lv = [(s.p, s.kind) for s in st["swings"] if not s.broken and not s.swept]
    return {"tf": series["tf"], "trend": st["trend"], "event": ev, "age": (len(cs) - 1 - ev.i) if ev else None, "levels": lv}


def category(score):
    if score >= 75:
        return "Setup kuat"
    if score >= 60:
        return "Setup potensial"
    if score >= 45:
        return "Setup spekulatif"
    return "WAIT"


def analyze(series, htf, price):
    cs = series["closed"][-MAX_ANALYSIS_CANDLES:]
    tf = series["tf"]
    n = TF_CONFIG[tf]["swing"]
    atr = atr_series(cs)
    a = atr[-1]
    if a <= 0:
        raise DataError("volatilitas nol; data tidak valid")
    st = analyze_structure(cs, atr, n)
    snr = build_snr(cs, st["swings"], a, price)
    snd = build_snd(cs, atr, st["events"])
    fvg = build_fvg(cs, atr)
    er = efficiency(cs)
    nlen = len(cs)
    last_ev = st["events"][-1] if st["events"] else None
    last_age = (nlen - 1 - last_ev.i) if last_ev else 9999
    recent = [e for e in st["events"] if nlen - 1 - e.i <= 35]
    if er < 0.22 or not recent:
        regime = "RANGING"
    elif er >= 0.3:
        regime = "TRENDING"
    else:
        regime = "TRANSISI"
    ctx = {"cs": cs, "atr": a, "price": price, "structure": st, "snr": snr, "snd": snd, "fvg": fvg,
           "pa": pa_scores(cs, a)}
    if htf:
        ctx["htf_levels"] = htf["levels"]
    w = dynamic_weights(regime, last_ev, last_age)
    tot = sum(w.values())
    w = {k: v * 100.0 / tot for k, v in w.items()}
    res = {"series": series, "price": price, "atr": a, "regime": regime, "er": er, "structure": st,
           "snr": snr, "snd": snd, "fvg": fvg, "htf": htf, "weights": w, "ctx": ctx, "dirs": {}}
    for d in ("BUY", "SELL"):
        comps, info = direction_components(d, ctx)
        pts = {k: comps[k] * w[k] for k in comps}
        total = sum(pts.values())
        adj = 0.0
        if htf and htf["trend"] != 0:
            aligned = (htf["trend"] > 0) == (d == "BUY")
            adj = 4.0 if aligned else -4.0
        res["dirs"][d] = {"comps": comps, "pts": pts, "info": info, "raw": total,
                          "score": clip((total + adj) / 100.0) * 100.0, "htf_adj": adj}
    b, s = res["dirs"]["BUY"]["score"], res["dirs"]["SELL"]["score"]
    best, other = ("BUY", "SELL") if b >= s else ("SELL", "BUY")
    bs, os_ = res["dirs"][best]["score"], res["dirs"][other]["score"]
    res["signal"], res["reason_wait"], res["trade"], res["zone"] = "WAIT", None, None, None
    # catatan terlambat (struktur searah tetapi harga sudah jauh dari zona)
    for d in (best, other):
        if res["dirs"][d]["comps"]["struct"] >= 0.6:
            zc = pick_entry(d, ctx)
            if zc is not None and zc["late"]:
                res["late_note"] = (d, zc)
                break
    if bs < 45:
        res["reason_wait"] = "Skor tertinggi %.0f (< 45): konfluensi belum cukup." % bs
    elif bs - os_ < 6 and bs < 65:
        res["reason_wait"] = "Skor BUY (%.0f) dan SELL (%.0f) saling berdekatan: struktur belum jelas arahnya." % (b, s)
    else:
        zone = pick_entry(best, ctx)
        if zone is None:
            res["reason_wait"] = "Arah condong %s (skor %.0f) tetapi tidak ada zona entry valid yang dekat harga." % (best, bs)
        else:
            trade, why = build_trade(best, ctx, zone)
            if trade is None:
                res["reason_wait"] = "Arah condong %s (skor %.0f) tetapi %s." % (best, bs, why)
            else:
                res.update({"signal": best, "trade": trade, "zone": zone})
    res["best"], res["best_score"] = best, bs
    return res


# =============================================================================
# FORMAT PESAN
# =============================================================================
def fp(x):
    return "%.2f" % x


def fmt_dur(sec):
    sec = int(max(0, sec))
    if sec < 3600:
        return "%d menit" % (sec // 60)
    if sec < 86400:
        return "%.1f jam" % (sec / 3600.0)
    return "%.1f hari" % (sec / 86400.0)


def fmt_wib(ts):
    return datetime.fromtimestamp(ts, tz=WIB).strftime("%d-%m %H:%M")


def strength_label(v):
    return "Kuat" if v >= 0.65 else ("Sedang" if v >= 0.4 else "Lemah")


def _esc(s):
    return html.escape(str(s), quote=False)


def structure_lines(res):
    cs = res["ctx"]["cs"]
    n = len(cs)
    price, a = res["price"], res["atr"]
    ev = res["structure"]["events"]
    lines = []

    def last_of(kind):
        for e in reversed(ev):
            if e.kind == kind:
                return e
        return None
    for kind in ("BOS", "CHOCH"):
        e = last_of(kind)
        if e is None:
            lines.append("• %s: tidak terdeteksi" % kind)
        else:
            lines.append("• %s: %s @ %s (%d candle lalu)" % (kind, "Bullish" if e.dirn == "bull" else "Bearish", fp(e.level), n - 1 - e.i))
    sup = [z for z in res["snr"] if z["mid"] <= price]
    rs = [z for z in res["snr"] if z["mid"] > price]
    sup.sort(key=lambda z: -z["mid"])
    rs.sort(key=lambda z: z["mid"])
    parts = []
    if sup:
        z = sup[0]
        parts.append("Support %s-%s (%s)" % (fp(z["low"]), fp(z["high"]), strength_label(z["strength"])))
    if rs:
        z = rs[0]
        parts.append("Resistance %s-%s (%s)" % (fp(z["low"]), fp(z["high"]), strength_label(z["strength"])))
    lines.append("• SNR: " + (" | ".join(parts) if parts else "tidak ada zona"))
    parts = []
    for kind, lab in (("demand", "Demand"), ("supply", "Supply")):
        zs = [z for z in res["snd"] if z["kind"] == kind and zone_dist("BUY" if kind == "demand" else "SELL", z, price, a) is not None]
        zs.sort(key=lambda z: zone_dist("BUY" if kind == "demand" else "SELL", z, price, a))
        if zs:
            z = zs[0]
            parts.append("%s %s-%s (%s)" % (lab, fp(z["low"]), fp(z["high"]), z["status"]))
    lines.append("• SND: " + (" | ".join(parts) if parts else "tidak ada zona aktif"))
    parts = []
    for kind, lab in (("bull", "Bullish"), ("bear", "Bearish")):
        zs = [z for z in res["fvg"] if z["kind"] == kind]
        zs.sort(key=lambda z: min(abs(price - z["low"]), abs(price - z["high"])))
        if zs:
            z = zs[0]
            parts.append("%s FVG %s-%s (%s)" % (lab, fp(z["low"]), fp(z["high"]), z["status"]))
    lines.append("• FVG: " + (" | ".join(parts) if parts else "tidak ada FVG terbuka"))
    h = res["htf"]
    if h:
        t = "Bullish" if h["trend"] > 0 else ("Bearish" if h["trend"] < 0 else "Netral")
        ev2 = ""
        if h["event"]:
            ev2 = ", %s %s" % (h["event"].kind, "bull" if h["event"].dirn == "bull" else "bear")
        lines.append("• Konteks %s: %s%s" % (h["tf"], t, ev2))
    else:
        lines.append("• Konteks TF lebih tinggi: tidak tersedia")
    return lines


def reasons_text(res, d):
    dd = res["dirs"][d]
    info = dd["info"]
    out = []
    if "event" in info:
        e, age = info["event"]
        out.append("%s %s terbentuk di %s (%d candle lalu, close konfirmasi)" % (e.kind, "bullish" if e.dirn == "bull" else "bearish", fp(e.level), age))
    if "sweep" in info:
        out.append("likuiditas %s disapu lalu ditolak (false breakout)" % ("low" if d == "BUY" else "high"))
    z = res["zone"]
    if z:
        where = "harga berada di dalam area" if z["dist"] <= 0 else "harga %.1f ATR dari area, menunggu retracement" % z["dist"]
        out.append("entry di konfluensi %s (%s), %s" % (" + ".join(z["srcs"]), z["status"], where))
    pa = []
    if info["rej"] >= 1:
        pa.append("rejection wick")
    if info["eng"] >= 1:
        pa.append("engulfing")
    if info["imp"] >= 1:
        pa.append("candle impulsif")
    if pa:
        out.append("konfirmasi price action: " + ", ".join(pa))
    h = res["htf"]
    if h and h["trend"] != 0:
        al = (h["trend"] > 0) == (d == "BUY")
        out.append("struktur %s %s dengan arah sinyal" % (h["tf"], "searah" if al else "berlawanan (risiko counter-trend, skor dikurangi)"))
    if not out:
        return "Konfluensi terbatas."
    txt = "; ".join(out)
    return txt[0].upper() + txt[1:] + "."


def format_result(res):
    s = res["series"]
    sym, tf = s["symbol"], s["tf"]
    sig = res["signal"]
    L = ["🟡 <b>SMC HYBRID ANALYST</b>", "",
         "<b>Market:</b> %s   <b>Timeframe:</b> %s" % (sym, tf), ""]
    regime = {"RANGING": "Ranging / sideways", "TRENDING": "Trending", "TRANSISI": "Transisi"}[res["regime"]]
    if res["regime"] == "TRENDING":
        regime += " Bullish" if res["structure"]["trend"] > 0 else " Bearish"
    if sig == "WAIT":
        L.append("⚪ <b>SINYAL: WAIT</b>")
    else:
        L.append("%s <b>SINYAL: %s</b> — %s" % ("🟢" if sig == "BUY" else "🔴", sig, category(res["dirs"][sig]["score"])))
    L.append("Kondisi: %s" % regime)
    L += ["", "📊 <b>STRUKTUR MARKET</b>"] + [_esc(x) for x in structure_lines(res)]
    if sig != "WAIT":
        t, z = res["trade"], res["zone"]
        L += ["", "🎯 <b>AREA TRADING</b>",
              "Entry: <code>%s – %s</code>" % (fp(t["entry_low"]), fp(t["entry_high"])),
              "Stop Loss: <code>%s</code>" % fp(t["sl"]),
              "TP1: <code>%s</code> (%s)" % (fp(t["tp1"]), _esc(t["tp1_note"])),
              "TP2: <code>%s</code> (%s)" % (fp(t["tp2"]), _esc(t["tp2_note"]))]
        if t.get("tp3") is not None:
            L.append("TP3: <code>%s</code> (%s)" % (fp(t["tp3"]), _esc(t["tp3_note"])))
        if z["dist"] > 0.5:
            L.append("⏳ Harga %.1f ATR dari area, jangan dikejar; tunggu retracement." % z["dist"])
        L += ["", "🔥 <b>SKOR SETUP: %.0f%%</b>" % res["dirs"][sig]["score"], "",
              "🧠 <b>ALASAN ENTRY</b>", _esc(reasons_text(res, sig)), "",
              "⚠️ <b>INVALIDASI</b>",
              "Setup batal bila candle %s close %s <code>%s</code> (di luar struktur invalidasi)." % (
                  tf, "di bawah" if sig == "BUY" else "di atas", fp(t["inv"]))]
    else:
        L += ["", "🧠 <b>ALASAN</b>", _esc(res["reason_wait"] or "")]
        ln = res.get("late_note")
        if ln:
            d, zc = ln
            L.append("⏳ Struktur %s sudah terbentuk tapi harga %.1f ATR dari zona (%s-%s); jangan dikejar, pantau retracement." % (
                d, zc["dist"], fp(zc["low"]), fp(zc["high"])))
    if s.get("stale"):
        L += ["", "⚠️ Data tidak segar (market tutup / feed tertunda). Jangan dieksekusi."]
    text = "\n".join(L)
    return text if len(text) <= 4000 else text[:3990] + "…"


def analyze_symbol_tf(symbol, tf, force=False):
    main = fetch_candles(symbol, tf, force)
    htf = None
    extra = []
    try:
        htf = htf_summary(fetch_candles(symbol, TF_CONFIG[tf]["htf"], force))
    except DataError as e:
        extra.append("Konteks %s tidak tersedia (%s); analisis memakai %s saja." % (TF_CONFIG[tf]["htf"], e, tf))
    closed = main["closed"]
    ref = main["forming"].c if main["forming"] else closed[-1].c
    atr_now = atr_series(closed[-MAX_ANALYSIS_CANDLES:])[-1]
    price, note = fetch_price(symbol, ref, atr_now)
    price_src = "tick"
    if price is None:
        price = ref
        price_src = "dari candle"
        extra.append("Harga tick tidak dipakai (%s); harga diambil dari candle." % note)
    elif note:
        extra.append(note)
    res = analyze(main, htf, price)
    res["price_src"] = price_src
    res["extra_warnings"] = extra
    return format_result(res)


# =============================================================================
# TELEGRAM
# =============================================================================
MAIN_TEXT = "🟡 <b>SMC HYBRID ANALYST</b>\n\nPilih market untuk dianalisis:"
_busy = set()


def kb_market():
    return InlineKeyboardMarkup([[InlineKeyboardButton("🥇 XAUUSD", callback_data="m:XAUUSD"),
                                  InlineKeyboardButton("₿ BTCUSD", callback_data="m:BTCUSD")]])


def kb_tf(sym):
    def b(tf):
        return InlineKeyboardButton(tf, callback_data="t:%s:%s" % (sym, tf))
    return InlineKeyboardMarkup([[b("M1"), b("M5"), b("M15"), b("M30")],
                                 [b("H1"), b("H4"), b("D1")],
                                 [InlineKeyboardButton("⬅️ Ganti market", callback_data="back")]])


def kb_result(sym, tf):
    return InlineKeyboardMarkup([[InlineKeyboardButton("🔄 ANALISIS ULANG", callback_data="r:%s:%s" % (sym, tf)),
                                  InlineKeyboardButton("🏠 MENU UTAMA", callback_data="menu")]])


async def safe_edit(message, text, markup=None):
    try:
        await message.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=markup, disable_web_page_preview=True)
    except BadRequest as e:
        if "not modified" in str(e).lower():
            return
        logger.warning("edit HTML gagal (%s); kirim teks polos", e)
        try:
            await message.edit_text(re.sub(r"<[^>]+>", "", text), reply_markup=markup)
        except BadRequest as e2:
            if "not modified" not in str(e2).lower():
                logger.error("edit gagal: %s", e2)


async def run_analysis(message, sym, tf, force):
    loop = asyncio.get_running_loop()
    try:
        text = await loop.run_in_executor(None, analyze_symbol_tf, sym, tf, force)
    except DataError as e:
        logger.warning("DataError %s %s: %s", sym, tf, e)
        text = "❌ <b>Data tidak tersedia</b>\n%s %s: %s\n\nCoba lagi sebentar lagi." % (sym, tf, _esc(e))
    except Exception:
        logger.exception("analisis gagal %s %s", sym, tf)
        text = "❌ Terjadi kesalahan internal saat menganalisis %s %s. Detail ada di log." % (sym, tf)
    await safe_edit(message, text, kb_result(sym, tf))


def _allowed(update):
    if not ALLOWED_USER_IDS:
        return True
    u = update.effective_user
    return u is not None and u.id in ALLOWED_USER_IDS


async def cmd_start(update, context):
    if not _allowed(update):
        return
    await update.effective_message.reply_text(MAIN_TEXT, parse_mode=ParseMode.HTML, reply_markup=kb_market())


async def on_callback(update, context):
    q = update.callback_query
    if q is None:
        return
    if not _allowed(update):
        await q.answer("Akses ditolak.", show_alert=True)
        return
    data = q.data or ""
    p = data.split(":")
    try:
        if data == "menu":
            await q.answer()
            await q.message.chat.send_message(MAIN_TEXT, parse_mode=ParseMode.HTML, reply_markup=kb_market())
        elif data == "back":
            await q.answer()
            await safe_edit(q.message, MAIN_TEXT, kb_market())
        elif len(p) == 2 and p[0] == "m" and p[1] in SYMBOLS:
            await q.answer()
            await safe_edit(q.message, "🟡 <b>SMC HYBRID ANALYST</b>\n\nMarket: <b>%s</b>\nPilih timeframe:" % p[1], kb_tf(p[1]))
        elif len(p) == 3 and p[0] in ("t", "r") and p[1] in SYMBOLS and p[2] in TF_CONFIG:
            chat_id = q.message.chat.id
            if chat_id in _busy:
                await q.answer("Analisis sebelumnya masih berjalan…")
                return
            await q.answer()
            _busy.add(chat_id)
            try:
                wait = "⏳ Mengambil data BiQuote & menganalisis %s %s…" % (p[1], p[2])
                if p[0] == "t":     # pesan hasil baru, terpisah dari menu
                    target = await q.message.chat.send_message(wait)
                else:               # analisis ulang: perbarui pesan hasil yang sama
                    target = q.message
                    await safe_edit(target, wait, None)
                await run_analysis(target, p[1], p[2], force=True)
            finally:
                _busy.discard(chat_id)
        else:
            await q.answer("Tombol tidak dikenali. Kirim /start.", show_alert=True)
    except Exception:
        logger.exception("callback gagal: %r", data)


async def on_error(update, context):
    logger.error("Error handler: %s", context.error)


def main():
    if not TELEGRAM_OK:
        print("Library belum terpasang. Jalankan:\n  pip install \"python-telegram-bot>=20\" requests")
        sys.exit(1)
    token = os.environ.get("TELEGRAM_BOT_TOKEN") or TELEGRAM_BOT_TOKEN
    if not token or token.startswith("ISI_"):
        print("Token belum diisi. Isi TELEGRAM_BOT_TOKEN di bagian KONFIGURASI atau set environment variable.")
        sys.exit(1)
    app = ApplicationBuilder().token(token).build()
    app.add_handler(CommandHandler(["start", "menu"], cmd_start))
    app.add_handler(CallbackQueryHandler(on_callback))
    app.add_error_handler(on_error)
    logger.info("SMC HYBRID ANALYST berjalan. Tekan Stop untuk berhenti.")
    app.run_polling(allowed_updates=["message", "callback_query"], drop_pending_updates=True)


if __name__ == "__main__":
    main()
