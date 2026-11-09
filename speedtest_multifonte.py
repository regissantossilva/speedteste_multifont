#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
speedtest_multifonte.py
=======================

Medidor de banda multi-origem, feito para escapar do "teste de operadora".

Por que não confiar só no Speedtest/Ookla?
  - O servidor escolhido quase sempre é hospedado pela própria operadora ou por
    um parceiro próximo (cache/peering), então o tráfego nem sai da rede dela.
  - Muitas operadoras priorizam/whitelistam faixas de speedtest e tráfego para
    CDNs famosas, mas não o tráfego comum.

O que este script faz de diferente:
  - Mede download e upload em várias origens independentes e externas à
    operadora (Cloudflare, Hetzner, DataPacket, CacheFly, instâncias públicas
    do LibreSpeed, Netflix/Fast.com).
  - Usa conexões novas, cache-busting e descarta o "slow start" do TCP.
  - Mede latência ociosa, jitter e BUFFERBLOAT (latência sob carga) — o
    bufferbloat é muito difícil de mascarar.
  - Compara fluxo único x múltiplos fluxos (revela shaping por conexão).
  - Roda o Ookla/Speedtest como referência e mostra o servidor usado, além do
    quanto ele difere das origens independentes.
  - Pode testar portas alternativas, curl HTTP/2 e HTTP/3, proxy/túnel
    (SOCKS/HTTP), saída por interface (WireGuard) e fluxos curtos
    (anti-elephant-flow).
  - Gera um diagnóstico automático e exporta JSON.

Uso básico:
    python3 speedtest_multifonte.py

Exemplos:
    # teste rápido (~40 s)
    python3 speedtest_multifonte.py --quick

    # só download, 3 fluxos, 10 s por origem, sem Ookla
    python3 speedtest_multifonte.py --duration 10 --streams 3 --no-upload \
        --no-bufferbloat --no-ookla

    # forçar IPv4 (ou IPv6) e escolher servidor Ookla específico
    python3 speedtest_multifonte.py --family ipv4 --ookla-server 12345

    # usar instâncias LibreSpeed específicas
    python3 speedtest_multifonte.py --librespeed-url https://fra.speedtest.clouvider.net/backend

    # medir através de um túnel SOCKS/HTTP (VPN, SSH -D, sing-box/xray)
    python3 speedtest_multifonte.py --proxy socks5h://127.0.0.1:1080

    # forçar a saída pela interface do WireGuard (Linux)
    python3 speedtest_multifonte.py --bind wg0 --quick

    # comparar portas e transportes na mesma origem
    python3 speedtest_multifonte.py --ports 443,8443,2053 --curl --http3

    # diagnosticar throttling de fluxos grandes (elephant flow)
    python3 speedtest_multifonte.py --compare-short

Requisitos:
    pip install requests
    (opcional) speedtest-cli  ->  pip install speedtest-cli
    (opcional) SOCKS           ->  pip install 'requests[socks]'
    (opcional) HTTP/3          ->  curl compilado com HTTP3

Aviso: meça de preferência por cabo, com a rede ociosa. Wi-Fi e outros
dispositivos consumindo banda distorcem o resultado.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import contextlib
import json
import math
import os
import random
import re
import shutil
import socket
import statistics
import subprocess
import sys
import threading
import time
import unicodedata
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Callable, Optional
from urllib.parse import urlsplit

import requests
import urllib3
from requests.adapters import HTTPAdapter

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

UA = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)
CHUNK = 256 * 1024
UPLOAD_PAYLOAD = 4 * 1024 * 1024  # 4 MiB por requisição de upload
LIBRESPEED_LIST = "https://librespeed.org/backend-servers/servers.php"
FAST_API = (
    "https://api.fast.com/netflix/speedtest/v2"
    "?https=true&token=YXNkZmFzZGxmbnNkYWZoYXNkZmhrYWxm&urlCount=5"
)

# ---------------------------------------------------------------------------
# utilidades
# ---------------------------------------------------------------------------

USE_COLOR = True

# Preenchidos por main() conforme as opções de linha de comando.
PROXIES: Optional[dict[str, str]] = None
BIND_IFACE: Optional[str] = None
CURL_BIN: Optional[str] = None


class C:
    BOLD = "\033[1m"
    DIM = "\033[2m"
    GREEN = "\033[32m"
    YELLOW = "\033[33m"
    RED = "\033[31m"
    CYAN = "\033[36m"
    RESET = "\033[0m"


def paint(text: str, color: str) -> str:
    if not USE_COLOR:
        return text
    return f"{color}{text}{C.RESET}"


def num(value: float, decimals: int = 1) -> str:
    """Formata número no padrão pt-BR (vírgula decimal)."""
    if value is None or (isinstance(value, float) and math.isnan(value)):
        return "—"
    return f"{value:,.{decimals}f}".replace(",", "X").replace(".", ",").replace("X", ".")


def percentile(values: list[float], p: float) -> Optional[float]:
    if not values:
        return None
    data = sorted(values)
    if len(data) == 1:
        return data[0]
    k = (len(data) - 1) * p
    lo, hi = math.floor(k), math.ceil(k)
    if lo == hi:
        return data[int(k)]
    return data[lo] + (data[hi] - data[lo]) * (k - lo)


def trunc(text: str, width: int) -> str:
    text = str(text)
    return text if len(text) <= width else text[: max(1, width - 1)] + "…"


def host_of(url: str) -> str:
    try:
        return urlsplit(url).hostname or url
    except Exception:
        return url


def short_error(exc: BaseException) -> str:
    text = str(exc).strip() or exc.__class__.__name__
    text = re.sub(r"\s+", " ", text)
    return text[:120]


def _family_works(host: str, family: int, timeout: float = 2.5) -> bool:
    try:
        infos = socket.getaddrinfo(host, 443, family, socket.SOCK_STREAM)
    except socket.gaierror:
        return False
    for info in infos[:2]:
        sock = None
        try:
            sock = socket.socket(info[0], info[1], info[2])
            sock.settimeout(timeout)
            sock.connect(info[4])
            return True
        except OSError:
            continue
        finally:
            if sock is not None:
                sock.close()
    return False


def resolve_family(requested: str) -> str:
    """Em 'auto', só força IPv4 se o IPv6 da rede estiver quebrado.

    Deixar o sistema escolher quando o IPv6 funciona permite que hosts
    IPv4-only continuem acessíveis; já forçar IPv4 evita o caso clássico de
    rede com AAAA anunciado mas sem rota IPv6 real.
    """
    if requested != "auto":
        return requested
    if _family_works("speed.cloudflare.com", socket.AF_INET6):
        return "auto"
    return "ipv4"


@contextlib.contextmanager
def force_family(family: str):
    """Força IPv4/IPv6 interceptando a resolução de nomes (vale para requests)."""
    if family not in ("ipv4", "ipv6"):
        yield
        return
    wanted = socket.AF_INET if family == "ipv4" else socket.AF_INET6
    original = socket.getaddrinfo

    def filtered(host, port, fam=0, type=0, proto=0, flags=0):
        return original(host, port, wanted, type, proto, flags)

    socket.getaddrinfo = filtered  # type: ignore[assignment]
    try:
        yield
    finally:
        socket.getaddrinfo = original  # type: ignore[assignment]


class Counter:
    __slots__ = ("lock", "bytes", "errors", "done")

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.bytes = 0
        self.errors: list[str] = []
        self.done = 0

    def add(self, n: int) -> None:
        with self.lock:
            self.bytes += n

    def error(self, msg: str) -> None:
        with self.lock:
            if len(self.errors) < 5:
                self.errors.append(msg)


def make_session(pool: int = 8) -> requests.Session:
    session = requests.Session()
    session.headers.update({"User-Agent": UA, "Accept": "*/*"})
    if PROXIES:
        session.proxies.update(PROXIES)
    adapter = HTTPAdapter(
        pool_connections=pool,
        pool_maxsize=pool,
        max_retries=0,
        pool_block=False,
    )
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    return session


def http_get(url: str, **kwargs) -> requests.Response:
    """requests.get que respeita --proxy (sem depender de variáveis de ambiente)."""
    if PROXIES:
        kwargs.setdefault("proxies", PROXIES)
    return requests.get(url, **kwargs)


def proxy_env() -> dict[str, str]:
    """Ambiente para subprocessos (Ookla/curl) seguirem o mesmo proxy."""
    env = os.environ.copy()
    if PROXIES:
        value = PROXIES.get("https") or PROXIES.get("http") or ""
        if value:
            env["HTTP_PROXY"] = value
            env["HTTPS_PROXY"] = value
            env["ALL_PROXY"] = value
            env.setdefault("NO_PROXY", "127.0.0.1,localhost,::1")
    return env


@contextlib.contextmanager
def bind_interface(ifname: Optional[str]):
    """Força as conexões Python a sair por uma interface (SO_BINDTODEVICE, Linux)."""
    if not ifname:
        yield
        return
    if not sys.platform.startswith("linux"):
        raise RuntimeError("--bind só é suportado no Linux (SO_BINDTODEVICE).")
    option = getattr(socket, "SO_BINDTODEVICE", None)
    if option is None:
        raise RuntimeError("SO_BINDTODEVICE indisponível neste kernel/sistema.")

    try:
        probe = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        probe.setsockopt(socket.SOL_SOCKET, option, ifname.encode())
        probe.close()
    except OSError as exc:
        raise RuntimeError(
            f"não foi possível usar a interface '{ifname}': {exc}. "
            "Verifique o nome (ip link) e as permissões."
        ) from exc

    original = socket.socket

    class BoundSocket(original):  # type: ignore[misc, valid-type]
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            try:
                self.setsockopt(socket.SOL_SOCKET, option, ifname.encode())
            except OSError:
                pass

    socket.socket = BoundSocket  # type: ignore[assignment,misc]
    try:
        yield
    finally:
        socket.socket = original  # type: ignore[assignment]


def interface_ip(ifname: Optional[str], family: str = "ipv4") -> Optional[str]:
    if not ifname:
        return None
    flag = "-4" if family == "ipv4" else "-6"
    try:
        out = subprocess.run(
            ["ip", flag, "-o", "addr", "show", "dev", ifname],
            capture_output=True, text=True, timeout=5,
        ).stdout
    except Exception:  # noqa: BLE001
        return None
    match = re.search(r"inet6?\s+([0-9a-fA-F:.]+)/", out)
    return match.group(1) if match else None


def find_curl() -> Optional[str]:
    return shutil.which("curl")


def curl_features(curl: str) -> str:
    try:
        out = subprocess.run([curl, "-V"], capture_output=True, text=True, timeout=10)
        return (out.stdout + out.stderr)
    except Exception:  # noqa: BLE001
        return ""


def curl_supports(curl: str, version: str) -> bool:
    features = curl_features(curl)
    if version == "http2":
        return "HTTP2" in features
    return "HTTP3" in features


def range_headers(
    min_size: int = 128 * 1024,
    max_size: int = 1_500 * 1024,
    span: int = 900_000_000,
) -> dict[str, str]:
    """Cabeçalhos de um fluxo curto com Range aleatório (anti-elephant-flow)."""
    size = random.randint(min_size, max_size)
    start = random.randint(0, span)
    return {"Range": f"bytes={start}-{start + size - 1}"}


# ---------------------------------------------------------------------------
# medições de carga (download / upload)
# ---------------------------------------------------------------------------


@dataclass
class ProbeResult:
    mbps: float
    peak_mbps: float
    seconds: float
    measured_bytes: int
    samples: int
    errors: list[str] = field(default_factory=list)


def _compute_probe(samples: list[tuple[float, int]], warmup: float) -> tuple[float, float, int]:
    window = [(t, b) for (t, b) in samples if t >= warmup - 1e-9]
    if len(window) < 2:
        return 0.0, 0.0, 0
    t0, b0 = window[0]
    t1, b1 = window[-1]
    span = t1 - t0
    if span <= 0.05:
        return 0.0, 0.0, 0
    mbps = (b1 - b0) * 8 / span / 1_000_000
    peak = 0.0
    for (ta, ba), (tb, bb) in zip(window, window[1:]):
        dt = tb - ta
        if dt > 0:
            peak = max(peak, (bb - ba) * 8 / dt / 1_000_000)
    return mbps, peak, b1 - b0


def download_probe(
    url_factory: Callable[[], str],
    duration: float,
    warmup: float,
    streams: int,
    ua: str = "",
    short_factory: Optional[Callable[[], tuple[str, dict[str, str]]]] = None,
) -> ProbeResult:
    end_ref: dict[str, float] = {}
    warm_ref: dict[str, float] = {}

    def make_worker() -> Callable[[], None]:
        def worker() -> None:
            session = make_session(pool=1 if short_factory else streams)
            while True:
                now = time.perf_counter()
                if "end" not in end_ref:
                    return
                if now >= end_ref["end"]:
                    return
                headers = {
                    "Cache-Control": "no-cache, no-store, max-age=0",
                    "Pragma": "no-cache",
                    "Accept-Encoding": "identity",
                    **({"User-Agent": ua} if ua else {}),
                }
                if short_factory:
                    url, extra = short_factory()
                    headers.update(extra)
                    # conexão nova a cada pedaço = muitos fluxos curtos
                    headers["Connection"] = "close"
                else:
                    url = url_factory()
                try:
                    with session.get(
                        url,
                        stream=True,
                        # conexão não pode demorar mais que a janela útil do teste,
                        # senão o timeout nunca aparece nas amostras
                        timeout=(max(1.5, min(6.0, duration - warmup)), 8),
                        headers=headers,
                    ) as resp:
                        if resp.status_code == 429:
                            counter.error("HTTP 429 (rate limit)")
                            # não insiste: insistir só prolonga o bloqueio
                            time.sleep(1.0)
                            continue
                        if resp.status_code >= 400:
                            raise RuntimeError(f"HTTP {resp.status_code}")
                        for chunk in resp.iter_content(CHUNK):
                            if not chunk:
                                continue
                            now = time.perf_counter()
                            if now >= end_ref["end"]:
                                return
                            if now >= warm_ref["warm"]:
                                # contador é compartilhado via closure abaixo
                                counter.add(len(chunk))
                except requests.exceptions.SSLError as exc:
                    counter.error(f"TLS: {short_error(exc)}")
                    time.sleep(0.3)
                except Exception as exc:  # noqa: BLE001
                    counter.error(short_error(exc))
                    time.sleep(0.15)

        return worker

    counter = Counter()
    t0 = time.perf_counter()
    end_ref["end"] = t0 + duration
    warm_ref["warm"] = t0 + warmup

    # run_load_probe controla o tempo; aqui só precisamos do relógio compartilhado.
    def wrapper() -> None:
        w = make_worker()
        w()

    result = _run_with_shared_clock(
        [wrapper for _ in range(streams)], duration, warmup, end_ref, warm_ref, counter
    )
    return result


def _run_with_shared_clock(
    workers: list[Callable[[], None]],
    duration: float,
    warmup: float,
    end_ref: dict[str, float],
    warm_ref: dict[str, float],
    counter: Counter,
) -> ProbeResult:
    samples: list[tuple[float, int]] = []
    samples_lock = threading.Lock()
    t0 = time.perf_counter()
    end_ref["end"] = t0 + duration
    warm_ref["warm"] = t0 + warmup
    end = end_ref["end"]

    threads = []
    for fn in workers:
        th = threading.Thread(target=fn, daemon=True)
        th.start()
        threads.append(th)

    while True:
        now = time.perf_counter()
        if now >= end:
            break
        time.sleep(min(0.25, max(0.0, end - now)))
        with counter.lock:
            b = counter.bytes
        with samples_lock:
            samples.append((time.perf_counter() - t0, b))

    for th in threads:
        th.join(timeout=2.0)

    with counter.lock:
        b_final = counter.bytes
        errors = list(counter.errors)
    with samples_lock:
        samples.append((min(time.perf_counter() - t0, duration), b_final))

    mbps, peak, measured = _compute_probe(samples, warmup)
    if measured == 0 and b_final > 0:
        span = max(duration - warmup, 0.5)
        mbps = b_final * 8 / span / 1_000_000

    return ProbeResult(
        mbps=round(mbps, 2),
        peak_mbps=round(peak, 2),
        seconds=round(duration - warmup, 1),
        measured_bytes=measured,
        samples=len(samples),
        errors=errors,
    )


def curl_download_probe(
    url_factory: Callable[[], str],
    duration: float,
    warmup: float,
    streams: int,
    version: str,
    short_factory: Optional[Callable[[], tuple[str, dict[str, str]]]] = None,
) -> ProbeResult:
    """Mede download disparando processos curl (TLS/fingerprint e HTTP/2-3 próprios)."""
    if not CURL_BIN:
        raise RuntimeError("curl não encontrado no PATH")
    end_ref: dict[str, float] = {}
    warm_ref: dict[str, float] = {}
    counter = Counter()

    base = [
        CURL_BIN, "-sS", "-o", os.devnull,
        "--connect-timeout", "5",
        "--no-progress-meter",
        "--http3-only" if version == "http3" else "--http2",
        "-H", "Cache-Control: no-cache",
        "-w", "%{size_download} %{time_starttransfer} %{time_total} %{http_code}\\n",
    ]
    if PROXIES:
        proxy = PROXIES.get("https") or PROXIES.get("http")
        if proxy:
            base += ["--proxy", proxy]
    if BIND_IFACE:
        base += ["--interface", BIND_IFACE]

    def make_worker() -> Callable[[], None]:
        def worker() -> None:
            while True:
                now = time.perf_counter()
                if "end" not in end_ref or now >= end_ref["end"]:
                    return
                remaining = end_ref["end"] - now
                if remaining < 0.5:
                    return
                headers: dict[str, str] = {}
                if short_factory:
                    url, headers = short_factory()
                    headers = {**headers, "Connection": "close"}
                else:
                    url = url_factory()
                cmd = base + ["--max-time", f"{remaining:.1f}"]
                for key, value in headers.items():
                    cmd += ["-H", f"{key}: {value}"]
                cmd.append(url)
                try:
                    proc = subprocess.run(
                        cmd,
                        capture_output=True,
                        text=True,
                        timeout=remaining + 10,
                        env=proxy_env(),
                    )
                except Exception as exc:  # noqa: BLE001
                    counter.error(short_error(exc))
                    continue
                lines = proc.stdout.strip().splitlines()
                http_code = 0
                if lines:
                    parts = lines[-1].split()
                    if parts:
                        try:
                            size = int(float(parts[0]))
                        except (TypeError, ValueError):
                            size = 0
                        if len(parts) >= 4:
                            try:
                                http_code = int(float(parts[3]))
                            except (TypeError, ValueError):
                                http_code = 0
                        if http_code == 429:
                            counter.error("HTTP 429 (rate limit)")
                            time.sleep(1.0)
                            continue
                        if 400 <= http_code and http_code != 429:
                            counter.error(f"HTTP {http_code}")
                            time.sleep(0.2)
                            continue
                        if size > 0:
                            counter.add(size)
                if proc.returncode not in (0, 28):
                    counter.error(
                        f"curl rc={proc.returncode}: {proc.stderr.strip()[:90]}"
                    )
                    time.sleep(0.2)

        return worker

    return _run_with_shared_clock(
        [make_worker() for _ in range(streams)],
        duration,
        warmup,
        end_ref,
        warm_ref,
        counter,
    )


class CountingBody:
    """Corpo de upload que conta bytes realmente entregues ao socket."""

    def __init__(self, data: bytes, counter: Counter, end: float, warmup_end: float):
        self._data = data
        self._pos = 0
        self._counter = counter
        self._end = end
        self._warmup_end = warmup_end

    def __len__(self) -> int:
        return len(self._data)

    def read(self, size: int = -1) -> bytes:
        if size is None or size < 0:
            size = len(self._data) - self._pos
        chunk = self._data[self._pos : self._pos + size]
        self._pos += len(chunk)
        now = time.perf_counter()
        if chunk and self._warmup_end <= now < self._end:
            self._counter.add(len(chunk))
        return chunk


def upload_probe(
    url: str,
    payload: bytes,
    duration: float,
    warmup: float,
    streams: int,
) -> ProbeResult:
    counter = Counter()
    end_ref: dict[str, float] = {}
    warm_ref: dict[str, float] = {}

    def make_worker() -> Callable[[], None]:
        def worker() -> None:
            session = make_session(pool=streams)
            while time.perf_counter() < end_ref["end"]:
                body = CountingBody(payload, counter, end_ref["end"], warm_ref["warm"])
                try:
                    resp = session.post(
                        url,
                        data=body,
                        timeout=(6, 15),
                        headers={
                            "Content-Type": "application/octet-stream",
                            "Cache-Control": "no-cache",
                            "Accept-Encoding": "identity",
                        },
                    )
                    _ = resp.content
                except Exception as exc:  # noqa: BLE001
                    counter.error(short_error(exc))
                    time.sleep(0.15)

        return worker

    return _run_with_shared_clock(
        [make_worker() for _ in range(streams)],
        duration,
        warmup,
        end_ref,
        warm_ref,
        counter,
    )


# ---------------------------------------------------------------------------
# latência e bufferbloat
# ---------------------------------------------------------------------------


@dataclass
class LatencyResult:
    median_ms: float
    jitter_ms: float
    samples: list[float] = field(default_factory=list)


def latency_probe(
    ping_factory: Callable[[], tuple[str, dict[str, str]]],
    samples: int = 7,
    ua: str = "",
) -> Optional[LatencyResult]:
    session = make_session(pool=2)
    values: list[float] = []
    failures = 0
    for i in range(samples + 2):
        url, headers = ping_factory()
        if ua:
            headers = {**headers, "User-Agent": ua}
        started = time.perf_counter()
        try:
            resp = session.get(url, headers=headers, timeout=(3, 5))
            _ = resp.content
        except Exception:  # noqa: BLE001
            failures += 1
            if failures >= 3:
                break
            continue
        failures = 0
        elapsed = (time.perf_counter() - started) * 1000
        if i >= 2:
            values.append(elapsed)
    if not values:
        return None
    jitter = (
        statistics.mean(abs(b - a) for a, b in zip(values, values[1:]))
        if len(values) > 1
        else 0.0
    )
    return LatencyResult(
        median_ms=round(statistics.median(values), 2),
        jitter_ms=round(jitter, 2),
        samples=[round(v, 2) for v in values],
    )


@dataclass
class BufferbloatResult:
    idle_ms: float
    loaded_ms: float
    loaded_max_ms: float
    increase_ms: float
    grade: str


def bufferbloat_probe(
    dl_factory: Callable[[], str],
    ping_factory: Callable[[], tuple[str, dict[str, str]]],
    idle_ms: float,
    duration: float,
    streams: int,
    ua: str = "",
) -> BufferbloatResult:
    samples: list[float] = []
    samples_lock = threading.Lock()
    stop = threading.Event()

    def pinger() -> None:
        session = make_session(pool=2)
        end = time.perf_counter() + duration
        while not stop.is_set() and time.perf_counter() < end:
            url, headers = ping_factory()
            if ua:
                headers = {**headers, "User-Agent": ua}
            started = time.perf_counter()
            try:
                resp = session.get(url, headers=headers, timeout=(3, 4))
                _ = resp.content
                elapsed = (time.perf_counter() - started) * 1000
                with samples_lock:
                    samples.append(elapsed)
            except Exception:  # noqa: BLE001
                pass

    pinger_thread = threading.Thread(target=pinger, daemon=True)
    pinger_thread.start()
    try:
        download_probe(dl_factory, duration, warmup=1.0, streams=streams, ua=ua)
    finally:
        stop.set()
        pinger_thread.join(timeout=2.0)

    if not samples:
        return BufferbloatResult(idle_ms, 0.0, 0.0, 0.0, "?")

    loaded = statistics.median(samples)
    loaded_max = max(samples)
    increase = max(0.0, loaded - idle_ms)
    if increase <= 30:
        grade = "A"
    elif increase <= 60:
        grade = "B"
    elif increase <= 100:
        grade = "C"
    elif increase <= 200:
        grade = "D"
    else:
        grade = "F"
    return BufferbloatResult(
        idle_ms=round(idle_ms, 2),
        loaded_ms=round(loaded, 2),
        loaded_max_ms=round(loaded_max, 2),
        increase_ms=round(increase, 2),
        grade=grade,
    )


# ---------------------------------------------------------------------------
# backends
# ---------------------------------------------------------------------------


@dataclass
class Backend:
    key: str
    label: str
    dl_factory: Callable[[], str]
    ul_url: Optional[str]
    ping_factory: Callable[[], tuple[str, dict[str, str]]]
    host: str = ""
    isp_hosted: bool = False
    note: str = ""
    ua: str = ""  # algumas origens rejeitam User-Agent de navegador
    transport: str = "requests"  # requests | curl
    short_factory: Optional[Callable[[], tuple[str, dict[str, str]]]] = None
    tags: dict = field(default_factory=dict)


def _rand() -> str:
    return f"{random.getrandbits(48):x}"


def make_cloudflare(port: int = 443) -> Backend:
    host = "speed.cloudflare.com" if port == 443 else f"speed.cloudflare.com:{port}"
    base = f"https://{host}"

    def short() -> tuple[str, dict[str, str]]:
        size = random.randint(200_000, 1_500_000)
        return f"{base}/__down?bytes={size}&r={_rand()}", {}

    return Backend(
        key=f"cloudflare:{port}",
        label="Cloudflare" if port == 443 else f"Cloudflare :{port}",
        # a Cloudflare recusa (403) pedidos muito grandes; 25 MB é o teto seguro
        dl_factory=lambda: f"{base}/__down?bytes=25000000&r={_rand()}",
        ul_url=f"{base}/__up",
        ping_factory=lambda: (f"{base}/__down?bytes=1&r={_rand()}", {}),
        host=host,
        short_factory=short,
        tags={"port": port},
    )


def make_curl_backend(version: str) -> Backend:
    base = "https://speed.cloudflare.com"
    label = f"Cloudflare via curl ({'HTTP/3' if version == 'http3' else 'HTTP/2'})"

    def short() -> tuple[str, dict[str, str]]:
        size = random.randint(200_000, 1_500_000)
        return f"{base}/__down?bytes={size}&r={_rand()}", {}

    return Backend(
        key=f"curl-{version}",
        label=label,
        dl_factory=lambda: f"{base}/__down?bytes=25000000&r={_rand()}",
        ul_url=None,
        ping_factory=lambda: (f"{base}/__down?bytes=1&r={_rand()}", {}),
        host="speed.cloudflare.com",
        transport="curl",
        short_factory=short,
        tags={"protocol": version},
    )


def make_hetzner() -> Backend:
    base = "https://ash-speed.hetzner.com/1GB.bin"
    return Backend(
        key="hetzner",
        label="Hetzner (Ashburn, EUA)",
        # query string faz o servidor da Hetzner derrubar a conexão
        dl_factory=lambda: base,
        ul_url=None,
        ping_factory=lambda: (base, {"Range": "bytes=0-0", "Cache-Control": "no-cache"}),
        host="ash-speed.hetzner.com",
        ua="curl/8.5.0",
        short_factory=lambda: (base, range_headers()),
    )


def make_datapacket() -> Backend:
    base = "https://ash.download.datapacket.com/1000mb.bin"
    return Backend(
        key="datapacket",
        label="DataPacket (Ashburn, EUA)",
        dl_factory=lambda: f"{base}?r={_rand()}",
        ul_url=None,
        ping_factory=lambda: (base, {"Range": "bytes=0-0", "Cache-Control": "no-cache"}),
        host="ash.download.datapacket.com",
        ua="curl/8.5.0",
        short_factory=lambda: (base, range_headers()),
    )


def make_cachefly() -> Backend:
    base = "https://cachefly.cachefly.net/100mb.test"
    return Backend(
        key="cachefly",
        label="CacheFly (CDN anycast)",
        dl_factory=lambda: f"{base}?r={_rand()}",
        ul_url=None,
        ping_factory=lambda: (base, {"Range": "bytes=0-0", "Cache-Control": "no-cache"}),
        host="cachefly.cachefly.net",
        ua="curl/8.5.0",
        short_factory=lambda: (base, range_headers()),
    )


def make_ovh() -> Backend:
    base = "https://proof.ovh.net/files/1Gb.dat"
    return Backend(
        key="ovh",
        label="OVH (Europa)",
        dl_factory=lambda: base,
        ul_url=None,
        ping_factory=lambda: (base, {"Range": "bytes=0-0", "Cache-Control": "no-cache"}),
        host="proof.ovh.net",
        ua="curl/8.5.0",
        short_factory=lambda: (base, range_headers()),
    )


def _normalize_librespeed_server(server: dict) -> Optional[dict]:
    srv = str(server.get("server", "")).strip()
    if srv.startswith("//"):
        srv = "https:" + srv
    if not srv.startswith("http"):
        return None
    server = dict(server)
    server["server"] = srv.rstrip("/") + "/"
    return server


def fetch_librespeed_servers(timeout: float = 15.0) -> list[dict]:
    resp = http_get(LIBRESPEED_LIST, timeout=timeout, headers={"User-Agent": UA})
    resp.raise_for_status()
    data = resp.json()
    if not isinstance(data, list):
        raise RuntimeError("lista do LibreSpeed em formato inesperado")
    out = []
    for item in data:
        if isinstance(item, dict):
            norm = _normalize_librespeed_server(item)
            if norm:
                out.append(norm)
    return out


def _librespeed_urls(server: dict) -> tuple[str, str, str]:
    base = server["server"]
    dl = str(server.get("dlURL") or "garbage.php").lstrip("/")
    ul = str(server.get("ulURL") or "empty.php").lstrip("/")
    ping = str(server.get("pingURL") or "empty.php").lstrip("/")
    return base + dl, base + ul, base + ping


def make_librespeed(server: dict) -> Backend:
    base = server["server"]
    dl_path, ul_path, ping_path = _librespeed_urls(server)
    name = server.get("name") or host_of(base)
    host = host_of(base)
    sponsor = str(server.get("sponsorName") or "")
    label = f"LibreSpeed · {name}"
    if sponsor and sponsor.lower() not in name.lower():
        label += f" ({sponsor})"
    return Backend(
        key=f"librespeed:{host}",
        label=label,
        dl_factory=lambda: f"{dl_path}?ckSize=100&r={_rand()}",
        ul_url=f"{ul_path}?r={_rand()}",
        ping_factory=lambda: (f"{ping_path}?r={_rand()}", {"Cache-Control": "no-cache"}),
        host=host,
        short_factory=lambda: (f"{dl_path}?ckSize=1&r={_rand()}", {}),
        tags={"sponsor": sponsor, "name": name},
    )


def make_fast() -> Optional[Backend]:
    """Netflix Fast.com. Pode apontar para cache/OCA dentro da operadora."""
    try:
        resp = http_get(FAST_API, timeout=12, headers={"User-Agent": UA})
        resp.raise_for_status()
        data = resp.json()
        targets = [t for t in data.get("targets", []) if t.get("url")]
        if not targets:
            return None
    except Exception:  # noqa: BLE001
        return None

    urls = [t["url"] for t in targets]
    host = host_of(urls[0])
    isp_hosted = bool(re.search(r"(^|[-.])isp([-.]|$)", host, re.I))
    client = data.get("client") or {}
    asn = str(client.get("asn") or "")
    if asn and asn in host:
        isp_hosted = True
    note = "cache/OCA da operadora" if isp_hosted else "CDN Netflix"
    idx = {"i": 0}

    def next_url() -> str:
        idx["i"] = (idx["i"] + 1) % len(urls)
        return urls[idx["i"]]

    return Backend(
        key="fast",
        label=f"Fast.com (Netflix) — {note}",
        dl_factory=next_url,
        ul_url=None,
        ping_factory=lambda: (urls[0], {"Range": "bytes=0-0", "Cache-Control": "no-cache"}),
        host=host,
        isp_hosted=isp_hosted,
        note=note,
        short_factory=lambda: (next_url(), range_headers(512 * 1024, 2 * 1024 * 1024)),
        tags={"client": client, "targets": urls},
    )


REGION_ALIASES = {
    "eu": ["europe", "germany", "netherlands", "france", "finland", "italy",
           "poland", "czech", "serbia", "greece", "london", "amsterdam",
           "frankfurt", "helsinki", "prague", "roma", "belgrade", "poz"],
    "us": ["united states", "usa", "atlanta", "chicago", "denver", "las vegas",
           "los angeles", "new york", "grand rapids"],
    "asia": ["japan", "tokyo", "singapore", "india", "korea", "hong kong"],
    "sa": ["brazil", "brasil", "argentina", "chile", "colombia", "peru", "uruguay"],
    "br": ["brazil", "brasil"],
}


def pick_librespeed_servers(
    count: int,
    region: Optional[str] = None,
    timeout: float = 5.0,
    verbose: bool = False,
) -> list[dict]:
    servers = fetch_librespeed_servers()
    if region:
        tokens = []
        for part in region.lower().split(","):
            part = part.strip()
            tokens.extend(REGION_ALIASES.get(part, [part]))
        filtered = [
            s for s in servers
            if any(tok in (s.get("name") or "").lower() for tok in tokens)
        ]
        if filtered:
            servers = filtered

    timings: dict[int, float] = {}

    def probe(server: dict) -> Optional[float]:
        _, _, ping_path = _librespeed_urls(server)
        started = time.perf_counter()
        try:
            resp = http_get(
                f"{ping_path}?r={_rand()}",
                timeout=timeout,
                headers={"User-Agent": UA, "Cache-Control": "no-cache"},
            )
            _ = resp.content
            return (time.perf_counter() - started) * 1000
        except Exception:  # noqa: BLE001
            return None

    with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
        futures = {pool.submit(probe, s): s for s in servers}
        for fut in concurrent.futures.as_completed(futures):
            server = futures[fut]
            try:
                ms = fut.result()
            except Exception:  # noqa: BLE001
                ms = None
            if ms is not None:
                timings[id(server)] = ms

    ranked = sorted(
        (s for s in servers if id(s) in timings), key=lambda s: timings[id(s)]
    )
    if verbose:
        for s in ranked[: min(10, len(ranked))]:
            print(f"    · {timings[id(s)]:7.1f} ms  {s.get('name')}", file=sys.stderr)

    picked: list[dict] = []
    sponsors: set[str] = set()
    for server in ranked:
        sponsor = str(server.get("sponsorName") or server.get("name") or "").lower()
        if sponsor in sponsors:  # evita 2 servidores do mesmo dono
            continue
        sponsors.add(sponsor)
        picked.append(server)
        if len(picked) >= count:
            break
    if not picked and ranked:
        picked = ranked[:count]
    return picked


# ---------------------------------------------------------------------------
# Ookla / Speedtest (referência oficial)
# ---------------------------------------------------------------------------


def find_ookla_cli() -> Optional[str]:
    """Prefere o speedtest-cli (Python), cujo JSON é estável e permite excluir servidores."""
    for name in ("speedtest-cli", "speedtest"):
        path = shutil.which(name)
        if not path:
            continue
        try:
            out = subprocess.run(
                [path, "--help"], capture_output=True, text=True, timeout=15
            )
            help_text = out.stdout + out.stderr
            # o binário oficial da Ookla usa -f json; o Python usa --json
            if "--json" in help_text:
                return path
        except Exception:  # noqa: BLE001
            continue
    return None


def detect_connection_info() -> dict:
    try:
        resp = http_get(
            "https://ipinfo.io/json", timeout=8, headers={"User-Agent": UA}
        )
        if resp.ok:
            return resp.json()
    except Exception:  # noqa: BLE001
        pass
    return {}


def _normalize(text: str) -> str:
    text = unicodedata.normalize("NFKD", text or "")
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    return re.sub(r"[^a-z0-9]+", " ", text.lower()).strip()


ISP_STOPWORDS = {
    "telecom", "telecomunicacoes", "internet", "servicos", "servico", "ltda",
    "brasil", "brazil", "empresa", "comunicacoes", "banda", "larga", "solucoes",
    "tecnologia", "net", "cia", "grupo", "holding", "sistema", "sistemas",
}

# nomes comerciais que não aparecem no campo "org" do ASN
ISP_ALIASES = {
    "telefonica": ["vivo"],
    "vivo": ["telefonica"],
    "claro": ["embratel", "net servicos"],
    "embratel": ["claro"],
    "oi": ["oibr"],
    "oibr": ["oi"],
    "algar": ["algartelecom"],
    "brisanet": ["brisa"],
}


def isp_tokens(org: str) -> list[str]:
    org = re.sub(r"^AS\d+\s*", "", org or "", flags=re.I)
    org = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", org)
    normalized = _normalize(org)
    tokens = [
        w for w in normalized.split()
        if len(w) >= 4 and w not in ISP_STOPWORDS
    ]
    for token in list(tokens):
        for alias in ISP_ALIASES.get(token, []):
            if alias not in tokens:
                tokens.append(alias)
    return tokens


def list_ookla_servers(cli: str) -> list[dict]:
    try:
        out = subprocess.run(
            [cli, "--list"], capture_output=True, text=True, timeout=90
        )
    except Exception:  # noqa: BLE001
        return []
    servers = []
    for line in out.stdout.splitlines():
        match = re.match(r"\s*(\d+)\)\s*(.+?)\s*\(([^)]*)\)", line)
        if match:
            servers.append(
                {
                    "id": match.group(1),
                    "sponsor": match.group(2).strip(),
                    "place": match.group(3).strip(),
                }
            )
    return servers


def auto_exclude_ookla(cli: str, connection: dict, verbose: bool) -> tuple[str, list[str]]:
    org = str(connection.get("org") or "")
    tokens = isp_tokens(org)
    if not tokens:
        return "", []
    servers = list_ookla_servers(cli)
    excluded = []
    for server in servers:
        sponsor = _normalize(server["sponsor"])
        if any(tok in sponsor for tok in tokens):
            excluded.append(f"{server['id']}:{server['sponsor']}")
    if verbose and excluded:
        print(f"    · servidores Ookla da operadora excluídos: {', '.join(excluded)}", file=sys.stderr)
    ids = ",".join(item.split(":", 1)[0] for item in excluded)
    return ids, excluded


def run_ookla(
    cli: str,
    server_id: Optional[str] = None,
    exclude_ids: Optional[str] = None,
    timeout: float = 120.0,
    source_ip: Optional[str] = None,
) -> dict:
    cmd = [cli, "--json", "--secure"]
    if server_id:
        cmd += ["--server", server_id]
    elif exclude_ids:
        cmd += ["--exclude", exclude_ids]
    if source_ip:
        cmd += ["--source", source_ip]
    env = proxy_env()
    started = time.perf_counter()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
    if proc.returncode != 0 or not proc.stdout.strip():
        # alguns servidores não aceitam HTTPS: tenta sem --secure
        cmd = [c for c in cmd if c != "--secure"]
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
    if proc.returncode != 0 or not proc.stdout.strip():
        raise RuntimeError((proc.stderr or proc.stdout or "falha no Ookla").strip()[-300:])
    data = json.loads(proc.stdout)
    server = data.get("server") or {}
    return {
        "download_mbps": round(float(data.get("download", 0)) * 8 / 1e6, 2),
        "upload_mbps": round(float(data.get("upload", 0)) * 8 / 1e6, 2),
        "ping_ms": round(float(data.get("ping", 0)), 2),
        "server_id": str(server.get("id", "")),
        "server_name": str(server.get("name", "")),
        "sponsor": str(server.get("sponsor", "")),
        "host": str(server.get("host", "")),
        "country": str(server.get("country", "")),
        "distance_km": round(float(server.get("d", 0) or 0), 1),
        "seconds": round(time.perf_counter() - started, 1),
    }


# ---------------------------------------------------------------------------
# orquestração
# ---------------------------------------------------------------------------


@dataclass
class RunConfig:
    duration: float
    warmup: float
    streams: int
    upload_streams: int
    family: str
    do_upload: bool
    do_bufferbloat: bool
    do_single: bool
    short_flows: bool
    verbose: bool


@dataclass
class BackendMeasurement:
    backend: Backend
    latency: Optional[LatencyResult] = None
    download: Optional[ProbeResult] = None
    upload: Optional[ProbeResult] = None
    bufferbloat: Optional[BufferbloatResult] = None
    single: Optional[ProbeResult] = None
    short_check: Optional[ProbeResult] = None
    error: str = ""

    def to_dict(self) -> dict:
        def probe(p: Optional[ProbeResult]) -> Optional[dict]:
            if p is None:
                return None
            return {
                "mbps": p.mbps,
                "peak_mbps": p.peak_mbps,
                "seconds": p.seconds,
                "bytes": p.measured_bytes,
                "errors": p.errors,
            }

        return {
            "key": self.backend.key,
            "label": self.backend.label,
            "host": self.backend.host,
            "isp_hosted": self.backend.isp_hosted,
            "transport": self.backend.transport,
            "tags": self.backend.tags,
            "latency_ms": self.latency.median_ms if self.latency else None,
            "jitter_ms": self.latency.jitter_ms if self.latency else None,
            "download": probe(self.download),
            "upload": probe(self.upload),
            "single_stream": probe(self.single),
            "short_flows_check": probe(self.short_check),
            "bufferbloat": (
                {
                    "idle_ms": self.bufferbloat.idle_ms,
                    "loaded_ms": self.bufferbloat.loaded_ms,
                    "increase_ms": self.bufferbloat.increase_ms,
                    "grade": self.bufferbloat.grade,
                }
                if self.bufferbloat
                else None
            ),
            "error": self.error,
        }


def build_backends(args: argparse.Namespace) -> list[Backend]:
    wanted = [b.strip().lower() for b in args.backends.split(",") if b.strip()]
    known = {"cloudflare", "hetzner", "datapacket", "cachefly", "ovh", "librespeed", "fast"}
    for name in wanted:
        if name not in known:
            print(
                pcolor(f"! origem desconhecida ignorada: {name}", C.YELLOW),
                file=sys.stderr,
            )
    backends: list[Backend] = []

    if "cloudflare" in wanted:
        ports: list[int] = []
        if args.ports:
            for item in args.ports.split(","):
                item = item.strip()
                if not item:
                    continue
                try:
                    port = int(item)
                except ValueError:
                    print(pcolor(f"! porta inválida ignorada: {item}", C.YELLOW), file=sys.stderr)
                    continue
                if not 1 <= port <= 65535:
                    print(pcolor(f"! porta fora do intervalo ignorada: {port}", C.YELLOW), file=sys.stderr)
                    continue
                if port not in ports:
                    ports.append(port)
        if 443 not in ports:
            ports.insert(0, 443)
        for port in ports:
            backends.append(make_cloudflare(port))
    elif args.ports:
        print(
            pcolor("! --ports só se aplica à origem cloudflare; ignorando.", C.YELLOW),
            file=sys.stderr,
        )

    if args.curl:
        if not CURL_BIN:
            print(pcolor("! curl não encontrado; backend curl desativado.", C.YELLOW), file=sys.stderr)
        elif not curl_supports(CURL_BIN, "http2"):
            print(pcolor("! curl sem suporte a HTTP/2; backend curl desativado.", C.YELLOW), file=sys.stderr)
        else:
            backends.append(make_curl_backend("http2"))

    if args.http3:
        if not CURL_BIN:
            print(pcolor("! curl não encontrado; HTTP/3 desativado.", C.YELLOW), file=sys.stderr)
        elif not curl_supports(CURL_BIN, "http3"):
            print(
                pcolor(
                    "! este curl não tem HTTP/3 (veja 'curl -V'); "
                    "backend HTTP/3 desativado.",
                    C.YELLOW,
                ),
                file=sys.stderr,
            )
        else:
            backends.append(make_curl_backend("http3"))

    if "hetzner" in wanted:
        backends.append(make_hetzner())
    if "datapacket" in wanted:
        backends.append(make_datapacket())
    if "cachefly" in wanted:
        backends.append(make_cachefly())
    if "ovh" in wanted:
        backends.append(make_ovh())

    if "librespeed" in wanted:
        custom = args.librespeed_url or []
        if custom:
            servers = []
            for url in custom:
                server = _normalize_librespeed_server(
                    {"server": url, "name": host_of(url), "sponsorName": ""}
                )
                if server:
                    servers.append(server)
        elif args.librespeed_all:
            servers = fetch_librespeed_servers()
        else:
            print(
                pcolor("→ descobrindo servidores LibreSpeed mais próximos…"),
                file=sys.stderr,
            )
            servers = pick_librespeed_servers(
                args.librespeed_n,
                region=args.librespeed_region,
                verbose=args.verbose,
            )
        for server in servers:
            backends.append(make_librespeed(server))

    if "fast" in wanted:
        fast = make_fast()
        if fast:
            backends.append(fast)
        else:
            print(
                pcolor("! Fast.com indisponível agora (API bloqueada); seguindo sem ele."),
                file=sys.stderr,
            )

    if not backends:
        raise SystemExit("Nenhum backend válido selecionado.")
    return backends


def pcolor(text: str, color: str = C.CYAN) -> str:
    return paint(text, color)


def measure_backend(
    backend: Backend, config: RunConfig, index: int, total: int
) -> BackendMeasurement:
    result = BackendMeasurement(backend=backend)
    prefix = f"[{index}/{total}]"
    print(
        f"{paint(prefix, C.DIM)} {paint(backend.label, C.BOLD)} "
        f"{paint('(' + backend.host + ')', C.DIM)}",
        file=sys.stderr,
        flush=True,
    )

    if backend.dl_factory is None:
        result.error = "sem endpoint de download"
        return result

    result.latency = latency_probe(backend.ping_factory, ua=backend.ua)
    if result.latency:
        print(
            f"    latência {num(result.latency.median_ms, 1)} ms · "
            f"jitter {num(result.latency.jitter_ms, 1)} ms",
            file=sys.stderr,
        )
    else:
        print(pcolor("    sem resposta a pings; tentando carga mesmo assim", C.YELLOW), file=sys.stderr)

    short_factory = backend.short_factory if config.short_flows else None
    try:
        if backend.transport == "curl":
            result.download = curl_download_probe(
                backend.dl_factory,
                config.duration,
                config.warmup,
                config.streams,
                backend.tags.get("protocol", "http2"),
                short_factory=short_factory,
            )
        else:
            result.download = download_probe(
                backend.dl_factory, config.duration, config.warmup, config.streams,
                ua=backend.ua, short_factory=short_factory,
            )
        mode = " · fluxos curtos" if short_factory else ""
        print(
            f"    download {paint(num(result.download.mbps, 1) + ' Mbps', C.GREEN)}"
            f" · pico {num(result.download.peak_mbps, 1)} Mbps{mode}",
            file=sys.stderr,
        )
        if result.download.mbps == 0 and result.download.errors:
            print(
                pcolor(
                    f"    sem dados: {result.download.errors[0]}",
                    C.YELLOW,
                ),
                file=sys.stderr,
            )
        elif result.download.errors and config.verbose:
            print(f"    avisos: {'; '.join(result.download.errors[:2])}", file=sys.stderr)
    except Exception as exc:  # noqa: BLE001
        result.error = short_error(exc)
        print(pcolor(f"    download falhou: {result.error}", C.RED), file=sys.stderr)

    if config.do_upload and backend.ul_url and result.download:
        try:
            payload = os.urandom(UPLOAD_PAYLOAD)
            result.upload = upload_probe(
                backend.ul_url,
                payload,
                config.duration,
                config.warmup,
                config.upload_streams,
            )
            print(
                f"    upload   {paint(num(result.upload.mbps, 1) + ' Mbps', C.GREEN)}"
                f" · pico {num(result.upload.peak_mbps, 1)} Mbps",
                file=sys.stderr,
            )
        except Exception as exc:  # noqa: BLE001
            print(pcolor(f"    upload falhou: {short_error(exc)}", C.RED), file=sys.stderr)

    return result


def run_suite(args: argparse.Namespace) -> dict:
    backends = build_backends(args)

    connection = detect_connection_info()
    if connection:
        print(
            f"    conexão: {connection.get('ip', '?')} · "
            f"{connection.get('org', '?')} · {connection.get('city', '')}/"
            f"{connection.get('country', '')}",
            file=sys.stderr,
        )

    # Referência oficial (Ookla)
    ookla = None
    ookla_meta: dict = {}
    if not args.no_ookla:
        cli = find_ookla_cli()
        if not cli:
            print(
                pcolor(
                    "! speedtest-cli (Python) não encontrado; comparação com Ookla "
                    "desativada. Instale com: pip install speedtest-cli",
                    C.YELLOW,
                ),
                file=sys.stderr,
            )
        else:
            exclude_ids = args.ookla_exclude or ""
            excluded: list[str] = []
            if not args.ookla_server and not exclude_ids and not args.ookla_no_exclude:
                exclude_ids, excluded = auto_exclude_ookla(
                    cli, connection, args.verbose
                )
            try:
                print(pcolor("→ rodando Ookla/Speedtest como referência…"), file=sys.stderr)
                source_ip = interface_ip(
                    args.bind,
                    "ipv6" if args.family == "ipv6" else "ipv4",
                )
                ookla = run_ookla(
                    cli,
                    server_id=args.ookla_server,
                    exclude_ids=exclude_ids or None,
                    source_ip=source_ip,
                )
                ookla_meta = {"excluded": excluded}
                print(
                    f"    servidor: {ookla['sponsor']} · {ookla['server_name']} · "
                    f"{ookla['distance_km']} km",
                    file=sys.stderr,
                )
            except Exception as exc:  # noqa: BLE001
                print(pcolor(f"! Ookla falhou: {short_error(exc)}", C.YELLOW), file=sys.stderr)

    config = RunConfig(
        duration=args.duration,
        warmup=args.warmup,
        streams=args.streams,
        upload_streams=args.upload_streams,
        family=args.family,
        do_upload=not args.no_upload,
        do_bufferbloat=not args.no_bufferbloat,
        do_single=not args.no_single,
        short_flows=args.short_flows,
        verbose=args.verbose,
    )

    if config.short_flows:
        without = [b.label for b in backends if not b.short_factory]
        if without:
            print(
                pcolor(
                    "! sem suporte a fluxos curtos (medidos no modo normal): "
                    + ", ".join(without),
                    C.YELLOW,
                ),
                file=sys.stderr,
            )

    extras = []
    if PROXIES:
        extras.append("via proxy")
    if BIND_IFACE:
        extras.append(f"interface {BIND_IFACE}")
    if config.short_flows:
        extras.append("fluxos curtos")
    suffix = (" · " + " · ".join(extras)) if extras else ""
    print(
        pcolor(
            f"\n→ {len(backends)} origem(ns) · {num(config.duration, 0)} s por teste · "
            f"{config.streams} fluxo(s) · {config.family}{suffix}",
            C.BOLD,
        ),
        file=sys.stderr,
    )

    measurements: list[BackendMeasurement] = []
    for i, backend in enumerate(backends, 1):
        measurements.append(measure_backend(backend, config, i, len(backends)))

    usable = [m for m in measurements if m.download and m.download.mbps > 0]
    if not usable:
        message = "Nenhuma origem conseguiu medir download. Verifique a conexão/firewall."
        if any(
            m.download and any("429" in err for err in m.download.errors)
            for m in measurements
        ):
            message += (
                " As origens responderam HTTP 429 (rate limit): aguarde alguns "
                "minutos e repita o teste."
            )
        raise SystemExit(message)

    # Para bufferbloat e fluxo único, preferimos uma origem fora da operadora:
    # medir no cache local dela não diz nada sobre o caminho real até a internet.
    independent_usable = [m for m in usable if not m.backend.isp_hosted]
    focus_pool = independent_usable or usable

    # Bufferbloat na origem independente mais rápida (download multi-fluxo)
    if config.do_bufferbloat and focus_pool:
        best = max(focus_pool, key=lambda m: m.download.mbps if m.download else 0)
        if best.latency and best.latency.median_ms > 0:
            print(
                pcolor(
                    f"\n→ medindo bufferbloat em {best.backend.label} "
                    f"(latência sob carga, {num(max(config.duration, 8.0), 0)} s)…"
                ),
                file=sys.stderr,
            )
            try:
                best.bufferbloat = bufferbloat_probe(
                    best.backend.dl_factory,
                    best.backend.ping_factory,
                    best.latency.median_ms,
                    max(config.duration, 8.0),
                    config.streams,
                    ua=best.backend.ua,
                )
                print(
                    f"    ociosa {num(best.bufferbloat.idle_ms, 1)} ms → "
                    f"sob carga {num(best.bufferbloat.loaded_ms, 1)} ms "
                    f"(+{num(best.bufferbloat.increase_ms, 1)} ms) · "
                    f"nota {best.bufferbloat.grade}",
                    file=sys.stderr,
                )
            except Exception as exc:  # noqa: BLE001
                print(pcolor(f"    bufferbloat falhou: {short_error(exc)}", C.YELLOW), file=sys.stderr)

    # Shaping por fluxo: repete a melhor origem independente com 1 fluxo
    if config.do_single and focus_pool:
        best = max(focus_pool, key=lambda m: m.download.mbps if m.download else 0)
        print(
            pcolor(f"\n→ comparando fluxo único x múltiplos fluxos em {best.backend.label}…"),
            file=sys.stderr,
        )
        try:
            if best.backend.transport == "curl":
                best.single = curl_download_probe(
                    best.backend.dl_factory,
                    config.duration,
                    config.warmup,
                    1,
                    best.backend.tags.get("protocol", "http2"),
                )
            else:
                best.single = download_probe(
                    best.backend.dl_factory,
                    config.duration,
                    config.warmup,
                    1,
                    ua=best.backend.ua,
                )
            ratio = (
                best.single.mbps / best.download.mbps
                if best.download and best.download.mbps
                else 0
            )
            print(
                f"    1 fluxo {num(best.single.mbps, 1)} Mbps · "
                f"{best.download.mbps and num(best.download.mbps, 1)} Mbps com "
                f"{config.streams} fluxos ({num(ratio * 100, 0)}%)",
                file=sys.stderr,
            )
        except Exception as exc:  # noqa: BLE001
            print(pcolor(f"    teste de fluxo único falhou: {short_error(exc)}", C.YELLOW), file=sys.stderr)

    # Elephant-flow: compara a melhor origem em fluxos curtos x fluxos longos
    if args.compare_short and not config.short_flows and focus_pool:
        best = max(focus_pool, key=lambda m: m.download.mbps if m.download else 0)
        if not best.backend.short_factory:
            print(
                pcolor("! origem escolhida não suporta fluxos curtos; comparação ignorada.", C.YELLOW),
                file=sys.stderr,
            )
        else:
            print(
                pcolor(
                    f"\n→ comparando fluxos longos x curtos em {best.backend.label}…"
                ),
                file=sys.stderr,
            )
            try:
                if best.backend.transport == "curl":
                    best.short_check = curl_download_probe(
                        best.backend.dl_factory,
                        config.duration,
                        config.warmup,
                        config.streams,
                        best.backend.tags.get("protocol", "http2"),
                        short_factory=best.backend.short_factory,
                    )
                else:
                    best.short_check = download_probe(
                        best.backend.dl_factory,
                        config.duration,
                        config.warmup,
                        config.streams,
                        ua=best.backend.ua,
                        short_factory=best.backend.short_factory,
                    )
                ratio = (
                    best.short_check.mbps / best.download.mbps
                    if best.download and best.download.mbps
                    else 0
                )
                print(
                    f"    longos {num(best.download.mbps, 1)} Mbps · "
                    f"curtos {num(best.short_check.mbps, 1)} Mbps "
                    f"({num(ratio * 100, 0)}%)",
                    file=sys.stderr,
                )
            except Exception as exc:  # noqa: BLE001
                print(
                    pcolor(f"    comparação de fluxos curtos falhou: {short_error(exc)}", C.YELLOW),
                    file=sys.stderr,
                )

    return {
        "connection": connection,
        "backends": measurements,
        "ookla": ookla,
        "ookla_meta": ookla_meta,
        "config": config,
        "proxy": (PROXIES.get("https") or PROXIES.get("http")) if PROXIES else None,
        "bind": BIND_IFACE,
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }


# ---------------------------------------------------------------------------
# análise e relatório
# ---------------------------------------------------------------------------


def analyze(data: dict) -> dict:
    measurements: list[BackendMeasurement] = data["backends"]
    ookla = data.get("ookla")
    analysis: dict = {"diagnostics": []}

    def is_distinct_origin(m: BackendMeasurement) -> bool:
        # variantes de porta e curl são diagnósticos da MESMA origem; não podem
        # pesar duas vezes na mediana independente
        return (
            not m.backend.isp_hosted
            and m.backend.transport != "curl"
            and m.backend.tags.get("port", 443) == 443
        )

    independent = [
        m for m in measurements
        if m.download and m.download.mbps > 0 and is_distinct_origin(m)
    ]
    dl_values = [m.download.mbps for m in independent if m.download]
    if not dl_values:
        dl_values = [
            m.download.mbps for m in measurements if m.download and m.download.mbps > 0
        ]

    if dl_values:
        median = statistics.median(dl_values)
        analysis["download_median_mbps"] = round(median, 2)
        analysis["download_p25_mbps"] = round(percentile(dl_values, 0.25), 2)
        analysis["download_min_mbps"] = round(min(dl_values), 2)
        analysis["download_max_mbps"] = round(max(dl_values), 2)
        if len(dl_values) > 1 and statistics.mean(dl_values) > 0:
            analysis["download_cv"] = round(
                statistics.pstdev(dl_values) / statistics.mean(dl_values), 3
            )
        analysis["download_sources"] = len(dl_values)

    ul_values = [
        m.upload.mbps for m in measurements
        if m.upload and m.upload.mbps > 0 and is_distinct_origin(m)
    ]
    if ul_values:
        analysis["upload_median_mbps"] = round(statistics.median(ul_values), 2)
        analysis["upload_p25_mbps"] = round(percentile(ul_values, 0.25), 2)

    if ookla and dl_values:
        median = statistics.median(dl_values)
        delta = (ookla["download_mbps"] - median) / median * 100 if median else 0
        analysis["ookla_vs_independent_pct"] = round(delta, 1)

    # diagnóstico
    diags = analysis["diagnostics"]
    if "download_median_mbps" in analysis:
        diags.append(
            {
                "level": "info",
                "text": (
                    f"Mediana independente de download: "
                    f"{num(analysis['download_median_mbps'])} Mbps "
                    f"(p25 {num(analysis['download_p25_mbps'])} Mbps, "
                    f"{analysis['download_sources']} origem(ns))."
                ),
            }
        )
        if analysis["download_median_mbps"] > 800:
            diags.append(
                {
                    "level": "info",
                    "text": (
                        "Acima de ~800 Mbps o próprio Python/requests pode virar "
                        "gargalo; confirme velocidades muito altas com uma ferramenta "
                        "nativa (ex.: iperf3 ou o binário oficial da Ookla)."
                    ),
                }
            )

    if ookla and dl_values:
        delta = analysis.get("ookla_vs_independent_pct", 0)
        if abs(delta) >= 25:
            direction = "acima" if delta > 0 else "abaixo"
            diags.append(
                {
                    "level": "warn",
                    "text": (
                        f"Ookla ficou {num(abs(delta))}% {direction} da mediana "
                        f"independente. Isso é compatível com priorização/whitelist de "
                        f"tráfego de speedtest, rota favorecida ou cache da operadora."
                    ),
                }
            )
        else:
            diags.append(
                {
                    "level": "good",
                    "text": "Ookla ficou próximo da mediana independente (diferença < 25%).",
                }
            )

    cv = analysis.get("download_cv")
    if cv is not None and cv >= 0.35:
        diags.append(
            {
                "level": "warn",
                "text": (
                    f"Grande dispersão entre origens (CV {num(cv * 100, 0)}%). "
                    "Pode haver peering ruim, throttling seletivo ou congestionamento."
                ),
            }
        )

    single_measure = next((m for m in measurements if m.single and m.download), None)
    if single_measure:
        ratio = single_measure.single.mbps / single_measure.download.mbps
        analysis["single_vs_multi_ratio"] = round(ratio, 3)
        if ratio < 0.6:
            diags.append(
                {
                    "level": "warn",
                    "text": (
                        f"Com 1 fluxo a vazão cai para {num(ratio * 100, 0)}% da obtida "
                        f"com múltiplos fluxos. Indício de shaping/limite por conexão."
                    ),
                }
            )
        else:
            diags.append(
                {
                    "level": "good",
                    "text": (
                        f"Fluxo único entrega {num(ratio * 100, 0)}% da vazão multi-fluxo "
                        "(sem sinal claro de limite por conexão)."
                    ),
                }
            )

    bb_measure = next((m for m in measurements if m.bufferbloat), None)
    if bb_measure and bb_measure.bufferbloat:
        bb = bb_measure.bufferbloat
        analysis["bufferbloat"] = {
            "grade": bb.grade,
            "increase_ms": bb.increase_ms,
            "loaded_ms": bb.loaded_ms,
            "idle_ms": bb.idle_ms,
        }
        if bb.grade in ("D", "F"):
            diags.append(
                {
                    "level": "warn",
                    "text": (
                        f"Bufferbloat nota {bb.grade}: latência sobe "
                        f"+{num(bb.increase_ms)} ms sob carga. A conexão satura e "
                        "prejudica jogos/vídeo em chamadas mesmo com 'muita banda'."
                    ),
                }
            )
        elif bb.grade == "C":
            diags.append(
                {
                    "level": "info",
                    "text": (
                        f"Bufferbloat nota C (+{num(bb.increase_ms)} ms sob carga). "
                        "Aceitável, mas há espaço para melhorar."
                    ),
                }
            )
        else:
            diags.append(
                {
                    "level": "good",
                    "text": (
                        f"Bufferbloat nota {bb.grade} (+{num(bb.increase_ms)} ms sob carga). "
                        "Boa resposta da rede sob saturação."
                    ),
                }
            )

    # Limite de requisições (HTTP 429): zera a medição e invalida comparações
    rate_limited = [
        m.backend.key for m in measurements
        if m.download and m.download.mbps == 0
        and any("429" in err for err in m.download.errors)
    ]
    if rate_limited:
        analysis["rate_limited"] = rate_limited
        diags.append(
            {
                "level": "warn",
                "text": (
                    "Origem(ns) bloquearam por excesso de requisições (HTTP 429): "
                    + ", ".join(rate_limited)
                    + ". As medições zeradas NÃO indicam shaping; aguarde alguns "
                    "minutos e repita (ou teste menos origens/portas de uma vez)."
                ),
            }
        )

    # Comparação entre portas alternativas da mesma origem (Cloudflare)
    base_443 = next(
        (m for m in measurements if m.backend.key == "cloudflare:443" and m.download),
        None,
    )
    alt_ports = [
        m for m in measurements
        if m.download and m.backend.key.startswith("cloudflare:")
        and m.backend.tags.get("port", 443) != 443
    ]
    if base_443 and base_443.download and alt_ports and not rate_limited:
        comparisons = []
        for m in alt_ports:
            port = m.backend.tags.get("port")
            ratio = m.download.mbps / base_443.download.mbps
            comparisons.append((port, m.download.mbps, ratio))
            analysis.setdefault("port_comparison", {})[str(port)] = {
                "mbps": m.download.mbps,
                "ratio_vs_443": round(ratio, 3),
            }
        best_port = max(comparisons, key=lambda item: item[1])
        worst_port = min(comparisons, key=lambda item: item[1])
        if best_port[2] >= 1.25:
            diags.append(
                {
                    "level": "warn",
                    "text": (
                        f"A porta {best_port[0]} entregou {num((best_port[2] - 1) * 100, 0)}% "
                        f"mais que a 443 na mesma origem. Indício de tratamento "
                        "diferenciado por porta."
                    ),
                }
            )
        elif worst_port[2] <= 0.75:
            diags.append(
                {
                    "level": "warn",
                    "text": (
                        f"A porta {worst_port[0]} entregou {num((1 - worst_port[2]) * 100, 0)}% "
                        f"menos que a 443. Pode ser shaping por porta ou bloqueio "
                        "parcial do CDN naquela porta."
                    ),
                }
            )
        else:
            diags.append(
                {
                    "level": "good",
                    "text": (
                        "Portas alternativas tiveram desempenho próximo da 443 "
                        "(sem sinal claro de shaping por porta)."
                    ),
                }
            )

    # Comparação de transporte (curl HTTP/2-3 x requests/HTTP1.1)
    curl_measure = next(
        (m for m in measurements if m.backend.transport == "curl" and m.download),
        None,
    )
    if (
        base_443 and base_443.download and curl_measure and curl_measure.download
        and not rate_limited
    ):
        ratio = curl_measure.download.mbps / base_443.download.mbps
        analysis["curl_vs_requests_ratio"] = round(ratio, 3)
        proto = "HTTP/3" if curl_measure.backend.tags.get("protocol") == "http3" else "HTTP/2"
        if ratio >= 1.25:
            diags.append(
                {
                    "level": "warn",
                    "text": (
                        f"curl/{proto} entregou {num((ratio - 1) * 100, 0)}% mais que "
                        "requests/HTTP1.1 na mesma origem. Pode haver tratamento "
                        "diferenciado por transporte/fingerprint TLS."
                    ),
                }
            )
        elif ratio <= 0.8:
            diags.append(
                {
                    "level": "info",
                    "text": (
                        f"curl/{proto} ficou {num((1 - ratio) * 100, 0)}% abaixo de "
                        "requests/HTTP1.1 (normal se a rede limita UDP ou se o "
                        "handshake HTTP/2 pesa em testes curtos)."
                    ),
                }
            )
        else:
            diags.append(
                {
                    "level": "good",
                    "text": (
                        f"curl/{proto} e requests/HTTP1.1 tiveram desempenho "
                        "equivalente (sem indício de tratamento por transporte)."
                    ),
                }
            )

    # Elephant flow: fluxos curtos x longos
    short_measure = next(
        (m for m in measurements if m.short_check and m.download), None
    )
    if (
        short_measure and short_measure.download and short_measure.short_check
        and short_measure.short_check.mbps > 0
    ):
        ratio = short_measure.short_check.mbps / short_measure.download.mbps
        analysis["short_vs_long_ratio"] = round(ratio, 3)
        if ratio >= 1.25:
            diags.append(
                {
                    "level": "warn",
                    "text": (
                        f"Fluxos curtos entregaram {num((ratio - 1) * 100, 0)}% MAIS que "
                        "fluxos longos. Isso sugere throttling de fluxos grandes "
                        "(elephant flow) e favorece a hipótese de shaping."
                    ),
                }
            )
        elif ratio <= 0.75:
            diags.append(
                {
                    "level": "info",
                    "text": (
                        f"Fluxos curtos entregaram {num((1 - ratio) * 100, 0)}% menos "
                        "(esperado: mais handshakes e menos tempo para encher o pipe)."
                    ),
                }
            )
        else:
            diags.append(
                {
                    "level": "good",
                    "text": (
                        "Fluxos curtos e longos tiveram desempenho parecido "
                        "(sem indício de throttling por tamanho de fluxo)."
                    ),
                }
            )

    if data.get("config") and data["config"].short_flows:
        diags.append(
            {
                "level": "info",
                "text": (
                    "Medição feita em fluxos curtos: os valores tendem a ficar abaixo "
                    "do normal por causa dos handshakes. Compare com uma execução sem "
                    "--short-flows."
                ),
            }
        )
    if data.get("proxy"):
        diags.append(
            {
                "level": "info",
                "text": (
                    "Medição feita através de proxy/túnel: o IP/ASN mostrado é o do "
                    "proxy. Compare com uma execução sem proxy para isolar a operadora."
                ),
            }
        )
    if data.get("bind"):
        diags.append(
            {
                "level": "info",
                "text": f"Saída forçada pela interface {data['bind']}.",
            }
        )

    errors = [m for m in measurements if m.error]
    if errors:
        diags.append(
            {
                "level": "info",
                "text": (
                    f"{len(errors)} origem(ns) falharam: "
                    + "; ".join(f"{m.backend.key}: {m.error}" for m in errors[:3])
                ),
            }
        )

    return analysis


def render_table(headers: list[str], rows: list[list[str]], aligns: Optional[list[str]] = None) -> str:
    if not rows:
        return ""
    aligns = aligns or ["<"] * len(headers)
    widths = []
    for i, header in enumerate(headers):
        widths.append(max([len(str(header))] + [len(str(row[i])) for row in rows]))
    lines = []
    header_line = "  ".join(
        f"{header:{aligns[i]}{widths[i]}}" for i, header in enumerate(headers)
    )
    lines.append(paint(header_line, C.BOLD))
    lines.append(paint("  ".join("─" * w for w in widths), C.DIM))
    for row in rows:
        lines.append(
            "  ".join(f"{str(cell):{aligns[i]}{widths[i]}}" for i, cell in enumerate(row))
        )
    return "\n".join(lines)


def print_report(data: dict, analysis: dict) -> None:
    measurements: list[BackendMeasurement] = data["backends"]
    ookla = data.get("ookla")
    config: RunConfig = data["config"]

    print()
    print(paint("═" * 78, C.CYAN))
    print(paint("  SPEEDTEST MULTIFONTE — resultado", C.BOLD))
    if data.get("connection"):
        conn = data["connection"]
        print(
            f"  {conn.get('ip', '?')} · {conn.get('org', '?')} · "
            f"{conn.get('city', '')}/{conn.get('country', '')} · "
            f"{data.get('family', 'auto')} · {data['timestamp']}"
        )
    extras = []
    if data.get("proxy"):
        extras.append(f"proxy {data['proxy']}")
    if data.get("bind"):
        extras.append(f"interface {data['bind']}")
    if config.short_flows:
        extras.append("fluxos curtos")
    if extras:
        print("  " + " · ".join(extras))
    print(paint("═" * 78, C.CYAN))

    latency_rows = []
    for m in measurements:
        if m.latency:
            latency_rows.append(
                [
                    trunc(m.backend.label, 42),
                    trunc(host_of(m.backend.host), 36),
                    num(m.latency.median_ms, 1),
                    num(m.latency.jitter_ms, 1),
                ]
            )
    if latency_rows:
        print("\n" + paint("LATÊNCIA (ociosa)", C.BOLD))
        print(render_table(
            ["origem", "host", "ms", "jitter ms"],
            latency_rows,
            ["<", "<", ">", ">"],
        ))

    dl_rows = []
    for m in measurements:
        if m.download:
            dl_rows.append(
                [
                    trunc(m.backend.label, 42) + (" *" if m.backend.isp_hosted else ""),
                    trunc(host_of(m.backend.host), 36),
                    num(m.download.mbps, 1),
                    "—" if m.backend.transport == "curl" else num(m.download.peak_mbps, 1),
                    str(m.download.seconds).replace(".", ","),
                ]
            )
    if dl_rows:
        print("\n" + paint(f"DOWNLOAD (multi-fluxo, {config.streams} conexões)", C.BOLD))
        print(render_table(
            ["origem", "host", "Mbps", "pico", "janela s"],
            dl_rows,
            ["<", "<", ">", ">", ">"],
        ))
        if any(m.backend.isp_hosted for m in measurements):
            print(paint("  * origem potencialmente hospedada dentro da operadora (fora da mediana)", C.DIM))

    if analysis.get("download_median_mbps") is not None:
        print("\n" + paint("AGREGADO INDEPENDENTE (download)", C.BOLD))
        print(
            f"  mediana ......... {paint(num(analysis['download_median_mbps']) + ' Mbps', C.GREEN)}"
        )
        print(f"  conservador p25 . {num(analysis['download_p25_mbps'])} Mbps")
        print(
            f"  faixa ........... {num(analysis['download_min_mbps'])} – "
            f"{num(analysis['download_max_mbps'])} Mbps"
        )
        if analysis.get("download_cv") is not None:
            print(f"  dispersão (CV) .. {num(analysis['download_cv'] * 100, 0)}%")

    ul_rows = []
    for m in measurements:
        if m.upload:
            ul_rows.append(
                [
                    trunc(m.backend.label, 42),
                    trunc(host_of(m.backend.host), 36),
                    num(m.upload.mbps, 1),
                    num(m.upload.peak_mbps, 1),
                ]
            )
    if ul_rows:
        print("\n" + paint(f"UPLOAD ({config.upload_streams} conexões)", C.BOLD))
        print(render_table(
            ["origem", "host", "Mbps", "pico"],
            ul_rows,
            ["<", "<", ">", ">"],
        ))
        if analysis.get("upload_median_mbps") is not None:
            print(
                f"  mediana independente: "
                f"{paint(num(analysis['upload_median_mbps']) + ' Mbps', C.GREEN)}"
            )

    bb = next((m.bufferbloat for m in measurements if m.bufferbloat), None)
    if bb:
        grade_color = C.GREEN if bb.grade in ("A", "B") else (C.YELLOW if bb.grade == "C" else C.RED)
        print("\n" + paint("BUFFERBLOAT (latência sob carga)", C.BOLD))
        print(
            f"  ociosa {num(bb.idle_ms, 1)} ms → sob carga {num(bb.loaded_ms, 1)} ms "
            f"(+{num(bb.increase_ms, 1)} ms) · pico {num(bb.loaded_max_ms, 1)} ms"
        )
        print(f"  nota: {paint(bb.grade, grade_color)}")

    single = next((m for m in measurements if m.single), None)
    if single and single.download:
        ratio = single.single.mbps / single.download.mbps * 100
        print("\n" + paint("FLUXO ÚNICO x MÚLTIPLOS FLUXOS", C.BOLD))
        print(
            f"  1 fluxo: {num(single.single.mbps)} Mbps · "
            f"{config.streams} fluxos: {num(single.download.mbps)} Mbps · "
            f"aproveitamento: {num(ratio, 0)}%"
        )

    short_measure = next((m for m in measurements if m.short_check), None)
    if (
        short_measure and short_measure.download and short_measure.short_check
        and short_measure.short_check.mbps > 0
    ):
        ratio = short_measure.short_check.mbps / short_measure.download.mbps * 100
        print("\n" + paint("FLUXOS LONGOS x CURTOS (anti-elephant-flow)", C.BOLD))
        print(
            f"  {short_measure.backend.label}: "
            f"longos {num(short_measure.download.mbps)} Mbps · "
            f"curtos {num(short_measure.short_check.mbps)} Mbps · "
            f"aproveitamento {num(ratio, 0)}%"
        )

    if ookla:
        print("\n" + paint("REFERÊNCIA OFICIAL (Ookla/Speedtest)", C.BOLD))
        print(
            f"  servidor: {ookla['sponsor']} · {ookla['server_name']} · "
            f"{ookla['host']} ({num(ookla['distance_km'])} km)"
        )
        if ookla["distance_km"] and ookla["distance_km"] < 50:
            print(
                paint(
                    "  servidor próximo: pode estar dentro de outra operadora; "
                    "para um teste mais neutro use --ookla-server <id>.",
                    C.DIM,
                )
            )
        print(
            f"  download {num(ookla['download_mbps'])} Mbps · "
            f"upload {num(ookla['upload_mbps'])} Mbps · ping {num(ookla['ping_ms'])} ms"
        )
        if analysis.get("ookla_vs_independent_pct") is not None:
            delta = analysis["ookla_vs_independent_pct"]
            color = C.YELLOW if abs(delta) >= 25 else C.GREEN
            print(
                f"  vs. mediana independente: "
                f"{paint(('+' if delta >= 0 else '') + num(delta) + '%', color)}"
            )
        if data.get("ookla_meta", {}).get("excluded"):
            print(
                paint(
                    "  servidores da operadora excluídos: "
                    + ", ".join(data["ookla_meta"]["excluded"]),
                    C.DIM,
                )
            )

    if analysis.get("diagnostics"):
        print("\n" + paint("DIAGNÓSTICO", C.BOLD))
        for diag in analysis["diagnostics"]:
            level = diag["level"]
            marker = {"warn": "⚠", "good": "✓", "info": "•"}.get(level, "•")
            color = {"warn": C.YELLOW, "good": C.GREEN, "info": C.CYAN}.get(level, C.CYAN)
            print(paint(f"  {marker} {diag['text']}", color))

    print("\n" + paint("─" * 78, C.DIM))
    print(
        paint(
            "Dica: repita em horários diferentes e, se possível, compare com e sem VPN. "
            "Se só o Ookla for alto, o tráfego de speedtest está sendo priorizado.",
            C.DIM,
        )
    )


def export_json(path: str, data: dict, analysis: dict) -> None:
    payload = {
        "timestamp": data["timestamp"],
        "connection": data.get("connection", {}),
        "config": {
            "duration_s": data["config"].duration,
            "warmup_s": data["config"].warmup,
            "streams": data["config"].streams,
            "family_requested": data["config"].family,
            "short_flows": data["config"].short_flows,
        },
        "ip_family": data.get("family", "auto"),
        "proxy": data.get("proxy"),
        "bind": data.get("bind"),
        "backends": [m.to_dict() for m in data["backends"]],
        "ookla": data.get("ookla"),
        "ookla_excluded": data.get("ookla_meta", {}).get("excluded", []),
        "analysis": analysis,
    }
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=2)
    print(f"\nJSON salvo em {path}")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def parse_args(argv: Optional[list[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Mede banda em várias origens independentes (Cloudflare, Hetzner, OVH, "
            "LibreSpeed, Netflix) e compara com o Ookla para detectar mascaramento."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "exemplos:\n"
            "  %(prog)s --quick\n"
            "  %(prog)s --duration 10 --streams 4\n"
            "  %(prog)s --backends cloudflare,librespeed --no-upload --no-ookla\n"
            "  %(prog)s --family ipv4 --json resultado.json\n"
            "  %(prog)s --proxy socks5h://127.0.0.1:1080 --quick\n"
            "  %(prog)s --bind wg0 --ports 443,8443 --curl --http3\n"
            "  %(prog)s --compare-short --json resultado.json\n"
        ),
    )
    parser.add_argument(
        "--duration", type=float, default=8.0,
        help="segundos de medição por origem (padrão: 8)",
    )
    parser.add_argument(
        "--warmup", type=float, default=1.5,
        help="segundos descartados no início de cada medição (padrão: 1.5)",
    )
    parser.add_argument(
        "--streams", type=int, default=4,
        help="conexões paralelas no download (padrão: 4)",
    )
    parser.add_argument(
        "--upload-streams", type=int, default=None,
        help="conexões paralelas no upload (padrão: igual a --streams)",
    )
    parser.add_argument(
        "--backends",
        default="cloudflare,librespeed,hetzner,datapacket,cachefly,fast",
        help=(
            "origens separadas por vírgula: cloudflare,librespeed,hetzner,"
            "datapacket,cachefly,ovh,fast (padrão: todas menos ovh)"
        ),
    )
    parser.add_argument(
        "--librespeed-n", type=int, default=2,
        help="quantas instâncias LibreSpeed usar (padrão: 2)",
    )
    parser.add_argument(
        "--librespeed-region", default=None,
        help="filtrar LibreSpeed por região: eu, us, asia, sa, br ou texto livre",
    )
    parser.add_argument(
        "--librespeed-url", action="append", default=[],
        help="URL de instância LibreSpeed (pode repetir)",
    )
    parser.add_argument(
        "--librespeed-all", action="store_true",
        help="usar todas as instâncias públicas do LibreSpeed (demorado)",
    )
    parser.add_argument(
        "--list-librespeed", action="store_true",
        help="listar instâncias públicas do LibreSpeed e sair",
    )
    parser.add_argument(
        "--family", choices=["auto", "ipv4", "ipv6"], default="auto",
        help="forçar família de IP (padrão: auto)",
    )
    parser.add_argument(
        "--proxy", default=None, metavar="URL",
        help=(
            "proxy/túnel para todos os testes: http://, https://, socks4://, "
            "socks5:// ou socks5h:// (SOCKS exige: pip install 'requests[socks]')"
        ),
    )
    parser.add_argument(
        "--bind", default=None, metavar="IFACE",
        help="forçar saída por uma interface, ex.: wg0 (Linux, SO_BINDTODEVICE)",
    )
    parser.add_argument(
        "--ports", default=None, metavar="LISTA",
        help=(
            "portas extras testadas na Cloudflare, ex.: 8443,2053,2083 "
            "(a 443 é sempre incluída)"
        ),
    )
    parser.add_argument(
        "--curl", action="store_true",
        help="adiciona uma origem medida via curl (HTTP/2, TLS fingerprint próprio)",
    )
    parser.add_argument(
        "--http3", action="store_true",
        help="adiciona uma origem via curl HTTP/3/QUIC (requer curl com HTTP3)",
    )
    parser.add_argument(
        "--short-flows", action="store_true",
        help="mede com muitos fluxos curtos (Range aleatório) para fugir de elephant-flow",
    )
    parser.add_argument(
        "--compare-short", action="store_true",
        help="compara a melhor origem em fluxos longos x curtos (diagnóstico)",
    )
    parser.add_argument("--no-upload", action="store_true", help="não medir upload")
    parser.add_argument("--no-bufferbloat", action="store_true", help="não medir bufferbloat")
    parser.add_argument("--no-single", action="store_true", help="não comparar fluxo único")
    parser.add_argument("--no-ookla", action="store_true", help="não rodar Ookla/Speedtest")
    parser.add_argument(
        "--ookla-server", default=None,
        help="ID do servidor Ookla (veja: speedtest-cli --list)",
    )
    parser.add_argument(
        "--ookla-exclude", default=None,
        help="IDs de servidores Ookla a excluir, separados por vírgula",
    )
    parser.add_argument(
        "--ookla-no-exclude", action="store_true",
        help="não excluir automaticamente servidores Ookla da operadora",
    )
    parser.add_argument("--json", dest="json_path", default=None, help="salvar resultado em JSON")
    parser.add_argument("--quick", action="store_true", help="preset rápido (~40 s)")
    parser.add_argument("--verbose", "-v", action="store_true", help="detalhes extras")
    parser.add_argument("--no-color", action="store_true", help="desativar cores")
    args = parser.parse_args(argv)

    if args.quick:
        if args.duration == 8.0:  # padrão não foi alterado pelo usuário
            args.duration = 4.0
        args.duration = max(args.duration, 4.0)
        args.warmup = min(args.warmup, 1.0)
        args.streams = min(args.streams, 4)
        args.librespeed_n = min(args.librespeed_n, 1)

    if args.upload_streams is None:
        args.upload_streams = args.streams
    if args.duration <= args.warmup + 1:
        parser.error("--duration precisa ser pelo menos --warmup + 1 segundo")
    if args.streams < 1 or args.upload_streams < 1:
        parser.error("--streams e --upload-streams devem ser >= 1")
    if args.short_flows and args.compare_short:
        print(
            pcolor(
                "! --compare-short não faz sentido com --short-flows; "
                "a comparação será ignorada.",
                C.YELLOW,
            ),
            file=sys.stderr,
        )
        args.compare_short = False
    return args


def main(argv: Optional[list[str]] = None) -> int:
    global USE_COLOR, PROXIES, BIND_IFACE, CURL_BIN

    # evita UnicodeEncodeError ao redirecionar saída no Windows
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")  # type: ignore[attr-defined]
        except Exception:  # noqa: BLE001
            pass

    args = parse_args(argv)
    USE_COLOR = sys.stdout.isatty() and not args.no_color and os.environ.get("NO_COLOR") is None

    if args.proxy:
        scheme = args.proxy.split("://", 1)[0].lower()
        if scheme not in ("http", "https", "socks4", "socks5", "socks5h"):
            print(
                pcolor(
                    "! --proxy deve começar com http://, https://, socks4://, "
                    "socks5:// ou socks5h://",
                    C.RED,
                ),
                file=sys.stderr,
            )
            return 2
        if scheme.startswith("socks"):
            try:
                import socks  # noqa: F401
            except ImportError:
                print(
                    pcolor(
                        "! proxy SOCKS requer PySocks: pip install 'requests[socks]'",
                        C.RED,
                    ),
                    file=sys.stderr,
                )
                return 2
        PROXIES = {"http": args.proxy, "https": args.proxy}
        # garante que o proxy seja usado também para destinos em NO_PROXY
        os.environ.pop("NO_PROXY", None)
        os.environ.pop("no_proxy", None)

    if args.bind:
        BIND_IFACE = args.bind
    if PROXIES and BIND_IFACE:
        print(
            pcolor(
                "! --proxy e --bind juntos: o socket até o proxy também será preso "
                "à interface; use um dos dois se o proxy for local.",
                C.YELLOW,
            ),
            file=sys.stderr,
        )
    CURL_BIN = find_curl()

    if args.list_librespeed:
        servers = fetch_librespeed_servers()
        for server in servers:
            print(f"{server.get('id', '?'):>4}  {server.get('name', ''):<48} {server['server']}")
        return 0

    os.environ.setdefault("PYTHONWARNINGS", "ignore")
    try:
        with bind_interface(BIND_IFACE):
            if PROXIES and args.family == "auto":
                # com túnel, a resolução/rota é do proxy: não vale forçar família
                family = "auto"
            else:
                family = resolve_family(args.family)
            if args.family == "auto":
                print(
                    f"    família de IP selecionada: {family}",
                    file=sys.stderr,
                )
            else:
                wanted_family = socket.AF_INET6 if family == "ipv6" else socket.AF_INET
                if not _family_works("speed.cloudflare.com", wanted_family):
                    print(
                        pcolor(
                            f"! {family} parece indisponível nesta rede; "
                            "os testes podem falhar.",
                            C.YELLOW,
                        ),
                        file=sys.stderr,
                    )
            with force_family(family):
                data = run_suite(args)
                data["family"] = family
        analysis = analyze(data)
        print_report(data, analysis)
        if args.json_path:
            export_json(args.json_path, data, analysis)
    except KeyboardInterrupt:
        print("\nInterrompido pelo usuário.", file=sys.stderr)
        return 130
    except requests.exceptions.RequestException as exc:
        print(f"Erro de rede: {short_error(exc)}", file=sys.stderr)
        return 1
    except RuntimeError as exc:
        print(f"Erro: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
