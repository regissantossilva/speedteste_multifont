# speedteste_multifont
analise speedtest avaliando varios destinos
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
