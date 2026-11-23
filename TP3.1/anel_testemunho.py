# /// script
# dependencies = ["marimo", "z3-solver"]
# requires-python = ">=3.14"
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium")

with app.setup:
    import marimo as mo
    import time
    from collections import deque
    import z3
    from z3 import (Bool, BoolVal, Int, If, And, Or, Not, Implies, Solver,
                    SolverFor, PbEq, Function, BoolSort, ForAll, Tactic, Then,
                    substitute, simplify, is_true, is_const, is_quantifier,
                    sat, unsat, Z3_OP_UNINTERPRETED)


# ---------------------------------------------------------------------------
# Introdução
# ---------------------------------------------------------------------------
@app.cell(hide_code=True)
def _():
    mo.md(r"""
    # TP3 — Exercício 1: exclusão mútua num anel com testemunho

    **Grupo 25.**

    ## O problema e a abordagem

    $N$ processos em anel; cada processo $i$ tem três booleanos: $w_i$ (à espera),
    $c_i$ (na secção crítica) e $t_i$ (tem o testemunho). Só o processo $0$ começa
    com o testemunho, e as regras *pedir*, *entrar*, *sair* e *passar* movem um único
    processo de cada vez. O estado de erro é "dois processos na secção crítica".

    Plano do notebook (segue as alíneas do enunciado):

    1. **SFOTS em Z3**, parametrizado por $N$ (classe `Anel`).
    2. **$k$-indução**: falha para $k$ pequeno, com um contra-exemplo inalcançável.
    3. **PDR** (`pdr_lia.py`, sem o reimplementar) e **interpolantes e invariantes**
       (`itp_mc`, com interpolantes calculados por CHCs/Spacer); o invariante
       obtido é verificado de forma independente (`e_invariante`).
    4. **Variante com regeneração** do testemunho: insegura, com traço de erro por **BMC**.
    5. **Comparação** para $N$ crescente: PDR, interpolantes e Spacer.

    Como referência independente usa-se uma **pesquisa em largura** sobre os estados
    alcançáveis, escrita em Python puro.

    **Ferramentas LLM.** Parte do código deste notebook foi escrita em diálogo com
    um assistente LLM (Claude). O código foi revisto e testado pelo grupo.
    """)
    return


# ---------------------------------------------------------------------------
# 1. SFOTS
# ---------------------------------------------------------------------------
@app.cell
def _():
    class Anel:
        """SFOTS proposicional do anel de N processos com testemunho.

        Um estado é um dicionário {'w': [...], 'c': [...], 't': [...]} com N
        variáveis por campo (w = à espera, c = secção crítica, t = testemunho).
        I, E e T recebem o estado como argumento, por isso podem ser
        instanciados sobre quantas cópias das variáveis se quiser.

        Com inteiro=True cada booleano é um Int (0 ou 1), que é o formato que
        o PDR de pdr_lia.py aceita.
        """

        def __init__(self, N, regenera=False, inteiro=False):
            assert N >= 2, "o anel precisa de pelo menos 2 processos"
            self.N, self.regenera, self.inteiro = N, regenera, inteiro
            if inteiro:
                self.X = {c: [Int(f"{c}{i}") for i in range(N)] for c in "wct"}
                self.Xp = {c: [Int(f"{c}{i}'") for i in range(N)] for c in "wct"}
            else:
                self.X = self.estado("0")    # variáveis de estado X
                self.Xp = self.estado("1")   # clones X'

        def estado(self, tag):
            """Cópia nova das variáveis de estado, com sufixo `tag`."""
            mk = Int if self.inteiro else Bool
            return {c: [mk(f"{c}{i}_{tag}") for i in range(self.N)] for c in "wct"}

        def vars(self, X):
            """Lista plana de todas as variáveis do estado X."""
            return [v for c in "wct" for v in X[c]]

        def V(self, v):
            """'A variável v é verdadeira'."""
            return (v == 1) if self.inteiro else v

        def atrib(self, v, b):
            """'A variável v toma o valor booleano b'."""
            if self.inteiro:
                return v == (1 if b else 0)
            return v == BoolVal(b)

        def dominio(self, X):
            """Restrição de domínio (só relevante com inteiros): cada variável em {0,1}."""
            if not self.inteiro:
                return BoolVal(True)
            return And([And(0 <= v, v <= 1) for v in self.vars(X)])

        def igual(self, X, Xp):
            """Os dois estados são iguais."""
            return And([a == b for a, b in zip(self.vars(X), self.vars(Xp))])

        def I(self, X):
            """Estado inicial: todos inativos e só o processo 0 tem o testemunho."""
            N = self.N
            inativos = [And(Not(self.V(X['w'][i])), Not(self.V(X['c'][i])))
                        for i in range(N)]
            return And(inativos + [self.V(X['t'][0])]
                       + [Not(self.V(X['t'][i])) for i in range(1, N)])

        def E(self, X):
            """Estado de erro: dois processos na secção crítica."""
            N = self.N
            return Or([And(self.V(X['c'][i]), self.V(X['c'][j]))
                       for i in range(N) for j in range(i + 1, N)])

        def regras(self, X, Xp):
            """Lista de (regra, processo, fórmula), uma por transição possível.

            Cada regra só altera as variáveis em `efeitos`; todas as outras
            mantêm o valor (condição de frame).
            """
            N = self.N

            def passo(guarda, efeitos):
                ef = [self.atrib(Xp[c][i], v) for (c, i), v in efeitos.items()]
                fr = [Xp[c][i] == X[c][i]
                      for c in "wct" for i in range(N) if (c, i) not in efeitos]
                return And([guarda] + ef + fr)

            L = []
            for i in range(N):
                j = (i + 1) % N
                w, c, t = self.V(X['w'][i]), self.V(X['c'][i]), self.V(X['t'][i])
                inativo = And(Not(w), Not(c))
                L.append(("pedir", i, passo(inativo, {('w', i): True})))
                L.append(("entrar", i, passo(And(w, t),
                                             {('w', i): False, ('c', i): True})))
                L.append(("sair", i, passo(c, {('c', i): False, ('t', i): False,
                                               ('t', j): True})))
                L.append(("passar", i, passo(And(inativo, t),
                                             {('t', i): False, ('t', j): True})))
                if self.regenera:
                    L.append(("regenerar", i, passo(And(w, Not(t)), {('t', i): True})))
            return L

        def T(self, X, Xp):
            """Relação de transição: um único processo se move numa das regras."""
            return Or([f for _, _, f in self.regras(X, Xp)])

    def anel(N, regenera=False):
        """Devolve o SFOTS do anel com N processos (com ou sem a regra regenerar)."""
        return Anel(N, regenera)

    def copias(S, n):
        """n+1 cópias independentes X_0..X_n das variáveis de estado."""
        return [S.estado(str(k)) for k in range(n + 1)]

    def valor(m, v):
        """Valor booleano de v no modelo m."""
        return is_true(m.eval(v, model_completion=True))

    def estado_modelo(S, m, X):
        """Extrai o estado X de um modelo, como dicionário de listas de bool."""
        return {c: [valor(m, X[c][i]) for i in range(S.N)] for c in "wct"}

    def mostra(S, est):
        """Texto de um estado: por processo, W=espera, C=crítica, T=testemunho."""
        return "  ".join(
            f"p{i}:" + "".join(c.upper() if est[c][i] else "." for c in "wct")
            for i in range(S.N))

    def inst(f, S, Y):
        """Instancia a fórmula f(X) (escrita sobre S.X) no estado Y."""
        return substitute(f, *zip(S.vars(S.X), S.vars(Y)))

    def tamanho(f):
        """Número de nós (partilhados) da fórmula f: mede a dimensão de um invariante."""
        vistos, pilha = set(), [f]
        while pilha:
            e = pilha.pop()
            if e.get_id() in vistos:
                continue
            vistos.add(e.get_id())
            pilha.extend(e.children())
        return len(vistos)

    return Anel, anel, copias, estado_modelo, inst, mostra, tamanho, valor


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito (alínea 1)

    * **`Anel`** é o SFOTS $\Sigma=\langle \mathsf{X},\mathsf{I},\mathsf{T},\mathsf{E}\rangle$.
      Um estado é um dicionário com três listas de $N$ booleanos Z3 (`w`, `c`, `t`).
    * `I`, `E` e `T` **recebem o estado como argumento**. Assim servem para qualquer
      cópia das variáveis ($\mathsf{X}_0,\dots,\mathsf{X}_k$), que o BMC, a $k$-indução
      e os interpolantes precisam.
    * `regras(X, X')` devolve uma fórmula por (regra, processo). Cada regra diz só o que
      muda; **todas as outras variáveis ficam iguais** (condição de frame). `T` é a
      disjunção de todas, por isso move-se um único processo de cada vez.
    * Com `regenera=True` acrescenta-se a regra *regenerar*.
    * Com `inteiro=True` os booleanos passam a inteiros em $\{0,1\}$. É a tradução usada mais
      à frente para o PDR de `pdr_lia.py`, que só aceita `Int`.
    * `copias`, `mostra`, `inst` e `tamanho` são auxiliares: criar cópias de variáveis,
      mostrar um estado (`W`, `C`, `T`), instanciar uma fórmula noutro estado e medir a
      dimensão de uma fórmula.
    """)
    return


# ---------------------------------------------------------------------------
# 2. k-indução e referência
# ---------------------------------------------------------------------------
@app.cell
def _(copias, estado_modelo):
    def k_inducao(S, k, inv=None):
        """k-indução para a propriedade P = ¬E (e, se dado, ∧ inv).

        Devolve {'base': bool, 'passo': bool, 'contraexemplo': lista de k+1
        estados ou None}. Com `inv` a propriedade é reforçada com esse invariante.
        """
        X = copias(S, k)
        cadeia = [S.T(X[s], X[s + 1]) for s in range(k)]

        def viola(Y):
            return Or(S.E(Y), Not(inv(S, Y))) if inv else S.E(Y)

        sb = Solver()                      # base: sem violação nos k primeiros estados
        sb.add(S.I(X[0]))
        for f in cadeia[:k - 1]:
            sb.add(f)
        sb.add(Or([viola(X[s]) for s in range(k)]))
        base = sb.check() == unsat

        sp = Solver()                      # passo: k estados bons => o seguinte é bom
        for f in cadeia:
            sp.add(f)
        for s in range(k):
            sp.add(Not(viola(X[s])))
        sp.add(viola(X[k]))
        r = sp.check()
        cex = None
        if r == sat:
            m = sp.model()
            cex = [estado_modelo(S, m, X[s]) for s in range(k + 1)]
        return {"base": base, "passo": r == unsat, "contraexemplo": cex}

    return (k_inducao,)


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito (alínea 2, parte 1)

    `k_inducao(S, k)` faz os dois testes da $k$-indução para a propriedade $\neg\mathsf{E}$:

    * **Caso base**: a partir de $\mathsf{I}$, ao longo de $k$ estados, nunca se chega a $\mathsf{E}$.
    * **Passo indutivo**: se $k$ estados consecutivos não são de erro, o seguinte também
      não é. O estado inicial *não* entra aqui, e é essa a fraqueza do método.

    Quando o passo falha, devolve o **contra-exemplo** (os $k+1$ estados do modelo do Z3).
    O parâmetro opcional `inv` reforça a propriedade com um invariante (usado no bónus).
    """)
    return


@app.cell
def _():
    def sucessores(N, est, regenera=False):
        """Transições do anel em Python puro (independentes do Z3).
        Um estado é um tuplo de N tuplos (w, c, t)."""
        for i in range(N):
            w, c, t = est[i]
            j = (i + 1) % N

            def com(mud):
                l = list(est)
                for k, v in mud.items():
                    l[k] = v
                return tuple(l)

            if not w and not c:
                yield ("pedir", i), com({i: (True, c, t)})
            if w and t:
                yield ("entrar", i), com({i: (False, True, t)})
            if c:
                yield ("sair", i), com({i: (w, False, False),
                                        j: (est[j][0], est[j][1], True)})
            if not w and not c and t:
                yield ("passar", i), com({i: (w, c, False),
                                          j: (est[j][0], est[j][1], True)})
            if regenera and w and not t:
                yield ("regenerar", i), com({i: (w, c, True)})

    def referencia(N, regenera=False):
        """Pesquisa em largura: (seguro, nº de estados alcançáveis, comprimento do
        traço de erro mais curto ou None)."""
        ini = tuple((False, False, i == 0) for i in range(N))
        dist = {ini: 0}
        fila = deque([ini])
        erro = None
        while fila:
            e = fila.popleft()
            if sum(c for _, c, _ in e) >= 2:
                erro = dist[e] if erro is None else min(erro, dist[e])
                continue
            for _, e2 in sucessores(N, e, regenera):
                if e2 not in dist:
                    dist[e2] = dist[e] + 1
                    fila.append(e2)
        return erro is None, len(dist), erro

    def alcancavel(N, est, regenera=False):
        """O estado `est` (dicionário de listas) é alcançável a partir do inicial?"""
        alvo = tuple((est['w'][i], est['c'][i], est['t'][i]) for i in range(N))
        ini = tuple((False, False, i == 0) for i in range(N))
        visto, fila = {ini}, deque([ini])
        while fila:
            e = fila.popleft()
            if e == alvo:
                return True
            for _, e2 in sucessores(N, e, regenera):
                if e2 not in visto:
                    visto.add(e2)
                    fila.append(e2)
        return False

    return alcancavel, referencia, sucessores


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito (referência independente)

    * `sucessores` reescreve as regras **em Python puro**, sem Z3.
    * `referencia(N)` é uma pesquisa em largura sobre todos os estados alcançáveis:
      diz se o sistema é seguro, quantos estados são alcançáveis e qual o traço de erro
      mais curto. É a "verdade" contra a qual se comparam o BMC, o PDR e os interpolantes.
    * `alcancavel(N, estado)` diz se um estado concreto é alcançável. Serve para
      explicar o contra-exemplo da $k$-indução.
    """)
    return


@app.cell
def _(alcancavel, anel, k_inducao, mostra):
    _S = anel(3)
    _linhas = []
    for _k in (1, 2, 3, 4):
        _r = k_inducao(_S, _k)
        _linhas.append(f"k={_k}:  base={_r['base']}   passo={_r['passo']}")
        if _r["contraexemplo"]:
            for _s, _e in enumerate(_r["contraexemplo"]):
                _linhas.append(f"    X{_s}: {mostra(_S, _e)}    "
                               f"alcançável a partir de I? {alcancavel(3, _e)}")
    mo.md("```\n" + "\n".join(_linhas) + "\n```")
    return


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito e o que se observa (alínea 2, parte 2)

    Para $N=3$ corre-se a $k$-indução com $k=1,\dots,4$ e, quando o passo falha, mostra-se o
    contra-exemplo (`W`=espera, `C`=secção crítica, `T`=testemunho) e se cada estado é
    alcançável.

    **Porque falha e porque o contra-exemplo não é acessível.** O primeiro estado de cada
    contra-exemplo ($\mathsf{X}_0$) é de um destes dois tipos: tem **dois testemunhos** (por
    exemplo `p0:W.T` e `p1:W.T`), ou tem um processo na secção crítica **sem testemunho**
    (por exemplo `p1:.C.`). A partir dele, as regras *entrar* e *sair* levam a dois processos
    em `C`. Mas estes estados não são alcançáveis (a coluna "alcançável?" dá `False`): as
    regras nunca criam testemunhos, só os movem, o estado inicial tem exatamente um, e só
    entra em `C` quem o tem. A $k$-indução não "sabe" isto, porque o passo indutivo parte de
    estados arbitrários. Para valores pequenos de $k$ há sempre um contra-exemplo deste tipo,
    e só um invariante que diga "há exatamente um testemunho e quem está em `C` tem-no" os
    elimina.
    """)
    return


# ---------------------------------------------------------------------------
# BMC e verificação independente
# ---------------------------------------------------------------------------
@app.cell
def _(copias, estado_modelo, mostra):
    def bmc(S, K):
        """Traço mais curto (≤ K passos) de I até E, ou None se não existir.
        Cada elemento é (regra, processo, estado); o primeiro tem regra None."""
        for n in range(K + 1):
            X = copias(S, n)
            s = Solver()
            s.add(S.I(X[0]))
            for k in range(n):
                s.add(S.T(X[k], X[k + 1]))
            s.add(S.E(X[n]))
            if s.check() == sat:
                m = s.model()
                traco = [(None, None, estado_modelo(S, m, X[0]))]
                for k in range(n):
                    nome, proc = next(
                        (nm, p) for nm, p, f in S.regras(X[k], X[k + 1])
                        if is_true(m.eval(f, model_completion=True)))
                    traco.append((nome, proc, estado_modelo(S, m, X[k + 1])))
                return traco
        return None

    def traco_str(S, traco):
        """Texto do traço: em cada passo, a regra, o processo e o estado."""
        linhas = []
        for k, (nome, proc, est) in enumerate(traco):
            mov = "início" if nome is None else f"{nome}(p{proc})"
            linhas.append(f"{k:2d}  {mov:14s} {mostra(S, est)}")
        return "\n".join(linhas)

    def conc(S, est):
        """Estado concreto (dicionário de BoolVal) a partir de um estado de bool."""
        return {c: [BoolVal(est[c][i]) for i in range(S.N)] for c in "wct"}

    def e_traco(S, traco):
        """Valida que o traço é mesmo um traço do SFOTS: começa em I, cada passo
        satisfaz T e acaba em E."""
        ests = [conc(S, e) for _, _, e in traco]
        ok = is_true(simplify(S.I(ests[0]))) and is_true(simplify(S.E(ests[-1])))
        for a, b in zip(ests, ests[1:]):
            ok = ok and is_true(simplify(S.T(a, b)))
        return ok

    return bmc, conc, e_traco, traco_str


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito (alínea 4, BMC)

    * `bmc(S, K)` procura, para $n=0,1,\dots,K$, um traço $\mathsf{X}_0\to\dots\to\mathsf{X}_n$
      com $\mathsf{I}(\mathsf{X}_0)$, $\mathsf{T}$ em cada passo e $\mathsf{E}(\mathsf{X}_n)$. Como $n$ cresce, o
      primeiro que encontra é **o mais curto**. Devolve `None` se não houver até $K$.
    * Para cada passo, descobre **qual a regra e qual o processo** que se moveram,
      avaliando no modelo a fórmula de cada regra.
    * `e_traco` valida o traço por conta própria: começa em $\mathsf{I}$, cada passo satisfaz $\mathsf{T}$
      e acaba em $\mathsf{E}$ (avaliando com valores concretos).
    """)
    return


@app.cell
def _():
    def e_invariante(S, inv):
        """Verificação independente de que inv(S, X) é um invariante indutivo que
        separa I de E: três testes de insatisfazibilidade, sem usar PDR nem
        interpolantes. Devolve (ok, resultado por teste)."""
        X, Xp = S.X, S.Xp
        testes = {
            "I ∧ ¬inv": [S.I(X), Not(inv(S, X))],
            "inv ∧ T ∧ ¬inv'": [inv(S, X), S.T(X, Xp), Not(inv(S, Xp))],
            "inv ∧ E": [inv(S, X), S.E(X)],
        }
        res = {}
        for nome, fs in testes.items():
            s = Solver()
            for f in fs:
                s.add(f)
            res[nome] = s.check() == unsat
        return all(res.values()), res

    return (e_invariante,)


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito (verificação independente de invariantes)

    `e_invariante(S, inv)` recebe um invariante como função `inv(S, X)` e faz os **três
    testes de insatisfazibilidade** do enunciado:

    1. $\mathsf{I}\land\neg\mathsf{inv}$: o invariante contém os estados iniciais;
    2. $\mathsf{inv}\land\mathsf{T}\land\neg\mathsf{inv}'$: é indutivo (um passo mantém-no);
    3. $\mathsf{inv}\land\mathsf{E}$: exclui os estados de erro.

    Não usa PDR nem interpolantes, por isso serve para confirmar o que eles devolvem.
    """)
    return


@app.cell
def _(anel, bmc, e_traco, referencia, traco_str):
    _linhas = []
    for _N in (2, 3, 4):
        for _reg in (False, True):
            _S = anel(_N, _reg)
            _seguro, _nest, _dist = referencia(_N, _reg)
            _tr = bmc(_S, 8)
            assert (_tr is None) == _seguro, (_N, _reg)
            if _tr:
                assert len(_tr) - 1 == _dist and e_traco(_S, _tr), (_N, _reg)
            _linhas.append(f"N={_N} regenera={str(_reg):5s}: "
                           f"{'seguro  ' if _seguro else 'INSEGURO'} "
                           f"{_nest:4d} estados alcançáveis, traço de erro mais curto: {_dist}")
    _S3 = anel(3, True)
    _t3 = bmc(_S3, 8)
    mo.md("**BMC contra a pesquisa em largura** (as asserções passaram):\n\n```\n"
          + "\n".join(_linhas)
          + "\n```\n\n**Traço de erro com BMC** ($N=3$, com regeneração):\n\n```\n"
          + "W = à espera, C = secção crítica, T = testemunho\n"
          + traco_str(_S3, _t3) + "\n```")
    return


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito e o que se observa

    Para $N=2,3,4$, com e sem a regra *regenerar*, compara-se o BMC com a pesquisa em largura:
    têm de concordar sobre se há erro **e** sobre o comprimento do traço mais curto, e o
    traço devolvido tem de ser um traço válido (`e_traco`). As asserções do código garantem-no.

    Sem regeneração o sistema é **seguro**: o BMC não encontra erro. Com regeneração é
    **inseguro**, com um traço de 5 passos. O traço mostra o mecanismo: um processo pede e,
    como está à espera sem testemunho, **regenera** um testemunho novo e entra em `C`;
    entretanto o processo que tinha o testemunho original pede e entra também, e ficam dois
    em `C`. O traço concreto pode variar com o modelo que o Z3 devolve, mas tem sempre
    5 passos, como confirma a pesquisa em largura.
    """)
    return


# ---------------------------------------------------------------------------
# 3a. PDR (pdr_lia.py)
# ---------------------------------------------------------------------------
@app.cell
async def _():
    from pdr_lia import app as _pdr_app

    _emb = await _pdr_app.embed()
    _defs = _emb.defs
    PDR = _defs["PDR"]
    e_modelo = _defs["e_modelo"]
    spacer_pdr = _defs["spacer"]
    # a classe CFA não é exportada pelo pdr_lia; obtém-se a partir de um exemplo
    CFA = type(next(iter(_defs["exemplos"]().values())))
    return CFA, PDR, e_modelo, spacer_pdr


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito (alínea 3, carregar o PDR)

    Importa-se o `pdr_lia.py` (que tem de estar na mesma pasta que este notebook) **sem o
    reimplementar**. Dele usam-se a classe `PDR`, a verificação `e_modelo` e a função
    `spacer`, que entrega as mesmas CHCs ao Spacer. A classe `CFA` não é exportada pelo
    `pdr_lia`, mas obtém-se como o tipo de qualquer um dos seus exemplos.
    """)
    return


@app.cell
def _(Anel, CFA, PDR):
    def anel_cfa(N, regenera=False):
        """Traduz o SFOTS do anel para um CFA de pdr_lia.py, com um só local de
        trabalho: system → do (inicialização), do → do (transição) e do → error
        (guarda E). Cada booleano é um Int restrito a {0,1}; as restrições de
        domínio entram na relação de todos os ramos."""
        S = Anel(N, regenera, inteiro=True)
        X, Xp = S.X, S.Xp
        ramos = {
            ("system", "do"): And(S.I(Xp), S.dominio(Xp)),
            ("do", "do"): And(S.dominio(X), S.T(X, Xp), S.dominio(Xp)),
            ("do", "error"): And(S.dominio(X), S.E(X), S.igual(X, Xp)),
        }
        nomes = [v.decl().name() for v in S.vars(X)]
        return S, CFA(nomes, ramos, f"anel N={N}, regenera={regenera}")

    def corre_pdr(cfa, max_N=12, max_passos=400):
        """Corre o PDR de pdr_lia.py. 'safe' (modelo das CHCs), 'unsafe' (caminho
        até error) ou 'unknown' (limites atingidos)."""
        pdr = PDR(cfa, max_N=max_N, max_passos=max_passos)
        t0 = time.time()
        res, tem = pdr.resolve()
        return {"resultado": {"sat": "safe", "unsat": "unsafe"}.get(res, "unknown"),
                "testemunha": tem, "frames": pdr.N, "obrigacoes": pdr.passos,
                "tempo": time.time() - t0}

    def inv_de_inteiros(f_int, N):
        """Converte um invariante sobre Int (variáveis w0, c0, t0, ...) num
        invariante booleano inv(S, X), para poder usar e_invariante."""
        nomes = [(c, i) for c in "wct" for i in range(N)]

        def inv(S, X):
            return substitute(f_int, *[(Int(f"{c}{i}"), If(X[c][i], 1, 0))
                                       for c, i in nomes])
        return inv

    return anel_cfa, corre_pdr, inv_de_inteiros


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito (alínea 3, tradução para o PDR)

    O PDR de `pdr_lia.py` só aceita **variáveis inteiras** e **CFAs**, por isso:

    * **Booleano → inteiro em $\{0,1\}$.** `Anel(N, inteiro=True)` escreve as mesmas
      regras com `v == 1` e `v == 0`. A restrição de domínio $0\le v\le 1$ está na relação
      $\tau$ de **todos** os ramos, para o PDR nunca considerar valores fora de $\{0,1\}$.
    * **CFA com um local de trabalho.** `system → do` tem como relação $\mathsf{I}(\mathsf{X}')$;
      `do → do` tem $\mathsf{T}(\mathsf{X},\mathsf{X}')$; `do → error` tem a guarda $\mathsf{E}(\mathsf{X})$ com
      $\mathsf{X}'=\mathsf{X}$. As CHCs são então: $P_{\mathsf{system}}$ vale sempre, $P_{do}$ contém $\mathsf{I}$ e é
      fechado por $\mathsf{T}$, e $P_{\mathsf{error}}$ tem de ser falso.
    * `corre_pdr` corre o algoritmo e normaliza o resultado: `sat`→`safe` (existe invariante),
      `unsat`→`unsafe` (caminho até `error`), senão `unknown`.
    * `inv_de_inteiros` converte o invariante de $P_{do}$ (sobre inteiros) para booleanos,
      para o poder verificar com `e_invariante`.
    """)
    return


# ---------------------------------------------------------------------------
# 3b. Interpolantes e invariantes
# ---------------------------------------------------------------------------
@app.cell
def _(copias, inst):
    def vars_livres(f):
        """Variáveis (constantes não interpretadas) que ocorrem em f."""
        vistos, res, pilha = set(), {}, [f]
        while pilha:
            e = pilha.pop()
            if e.get_id() in vistos:
                continue
            vistos.add(e.get_id())
            if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED:
                res[e.get_id()] = e
            else:
                pilha.extend(e.children())
        return list(res.values())

    def tem_quantificador(f):
        vistos, pilha = set(), [f]
        while pilha:
            e = pilha.pop()
            if e.get_id() in vistos:
                continue
            vistos.add(e.get_id())
            if is_quantifier(e):
                return True
            pilha.extend(e.children())
        return False

    def sem_quantificadores(f):
        """Elimina quantificadores de f com a tática 'qe' (domínio finito)."""
        if not tem_quantificador(f):
            return simplify(f)
        return Then(Tactic('qe'), Tactic('simplify'))(f).as_expr()

    def interpolate(A, B, comuns, timeout_ms=20000):
        """Interpolante de (A, B) sobre as variáveis `comuns`, calculado com CHCs.

        Resolve  A → Itp(comuns)  e  Itp(comuns) ∧ B → False  com o Spacer. O
        modelo dá o interpolante. Devolve None se A ∧ B for satisfazível (não há
        interpolante); levanta RuntimeError se o Spacer responder 'unknown'.
        """
        Itp = Function("Itp", *([BoolSort()] * len(comuns)), BoolSort())
        vA = vars_livres(A) + [v for v in comuns if v.get_id() not in
                               {w.get_id() for w in vars_livres(A)}]
        vB = vars_livres(B) + [v for v in comuns if v.get_id() not in
                               {w.get_id() for w in vars_livres(B)}]
        s = SolverFor("HORN")
        s.set("timeout", timeout_ms)
        s.add(ForAll(vA, Implies(A, Itp(*comuns))))
        s.add(ForAll(vB, Implies(And(Itp(*comuns), B), False)))
        r = s.check()
        if r == unsat:
            return None
        if r != sat:
            raise RuntimeError("o Spacer respondeu 'unknown' ao calcular o interpolante")
        return sem_quantificadores(s.model().eval(Itp(*comuns)))

    def itp_mc(S, m_max=12, max_iter=30):
        """Algoritmo de interpolantes e invariantes (model checking por interpolação).

        Para cada m = 0, 1, ...: parte-se de R = I e repete-se
          A = R(X0) ∧ T(X0,X1)           B = T(X1,X2) ∧ ... ∧ T(Xm,Xm+1) ∧ (E em X1..Xm+1)
        Se A ∧ B é insatisfazível, o interpolante I1 (sobre X1) sobre-aproxima os
        sucessores de R e não chega a E em m passos. Se I1 → R, então R é um
        invariante indutivo ('safe'). Senão R := R ∨ I1 (majorante). Se A ∧ B é
        satisfazível com R = I, há erro real ('unsafe'); com R ≠ I é um falso
        alarme e incrementa-se m.

        Devolve {'resultado': 'safe'|'unsafe'|'unknown', 'invariante', 'nm': (n, m),
        'iteracoes', 'tempo'}, com n = nº de majorantes acumulados em R e m a janela
        de erro em que se decidiu.
        """
        t0 = time.time()

        def vazio(*fs):
            s = Solver()
            for f in fs:
                s.add(f)
            return s.check() == unsat

        def saida(res, inv, nm, it):
            return {"resultado": res, "invariante": inv, "nm": nm,
                    "iteracoes": it, "tempo": time.time() - t0}

        if not vazio(S.I(S.X), S.E(S.X)):
            return saida("unsafe", None, (0, 0), 0)
        iteracoes = 0
        for m in range(m_max + 1):
            R = S.I(S.X)
            n = 0
            while True:
                X = copias(S, m + 1)
                A = And(inst(R, S, X[0]), S.T(X[0], X[1]))
                B = And([S.T(X[k], X[k + 1]) for k in range(1, m + 1)]
                        + [Or([S.E(X[k]) for k in range(1, m + 2)])])
                s = Solver()
                s.add(A)
                s.add(B)
                if s.check() == sat:
                    if n == 0:                       # R = I: contra-exemplo real
                        return saida("unsafe", None, (n, m), iteracoes)
                    break                            # falso alarme: aumenta m
                I1 = interpolate(A, B, S.vars(X[1]))
                I1 = substitute(I1, *zip(S.vars(X[1]), S.vars(S.X)))
                iteracoes += 1
                if vazio(I1, Not(R)):                # I1 → R: ponto fixo
                    return saida("safe", simplify(R), (n, m), iteracoes)
                R = Or(R, I1)
                n += 1
                if n > max_iter:
                    break
        return saida("unknown", None, (None, None), iteracoes)

    return interpolate, itp_mc, sem_quantificadores, vars_livres


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito (alínea 3, interpolantes e invariantes)

    O repositório LC não traz o algoritmo de interpolantes nem a função `interpolate`, por
    isso foram escritos aqui.

    * **`interpolate(A, B, comuns)`** calcula o interpolante **via CHCs**: pede ao Spacer um
      predicado `Itp` sobre as variáveis comuns tal que $A\to \mathit{Itp}$ e
      $\mathit{Itp}\land B\to\mathtt{False}$. O modelo do Spacer é o interpolante. Se o resultado
      tiver quantificadores, eliminam-se com `Tactic('qe')` (o domínio é finito). Se
      $A\land B$ for satisfazível não há interpolante e devolve `None`.
    * **`itp_mc(S)`** é o algoritmo de interpolantes e invariantes. Para cada janela de erro
      $m$, começa com $R=\mathsf{I}$ e calcula o interpolante de
      $A=R\land\mathsf{T}$ contra $B=$ "erro em $\le m$ passos". O interpolante sobre-aproxima o
      que se alcança em um passo a partir de $R$ sem chegar a erro.
        * se **implica $R$**, então $R$ é fechado por $\mathsf{T}$ e é o **invariante indutivo** (`safe`);
        * senão faz-se $R := R\lor I_1$ (**rotina do majorante**) e repete-se;
        * se $A\land B$ é satisfazível com $R=\mathsf{I}$, o erro é real (`unsafe`); com $R\neq\mathsf{I}$ é um
          falso alarme e aumenta-se $m$.
    * O par **$(n,m)$** devolvido é: $n$ = número de majorantes acumulados em $R$ e $m$ = janela de
      erro em que se decidiu ($n=0$ é um contra-exemplo genuíno a partir de $\mathsf{I}$).
    * O número de **iterações** é o total de interpolantes calculados, e a dimensão do invariante
      é medida com `tamanho`.

    O limite de iterações (`max_iter`) e o de janelas (`m_max`) ficam ao critério do grupo.
    """)
    return


# ---------------------------------------------------------------------------
# 3 e 4: execução
# ---------------------------------------------------------------------------
@app.cell
def _(anel, anel_cfa, corre_pdr, e_invariante, e_modelo, inst, inv_de_inteiros,
      itp_mc, tamanho):
    _N = 3
    _S = anel(_N)
    _, _cfa = anel_cfa(_N)
    _rp = corre_pdr(_cfa)
    _ri = itp_mc(_S)
    def _corta(f, n=500):
        s = str(f)
        return s if len(s) <= n else s[:n] + f"\n... (cortado; {len(s)} caracteres)"

    _txt = [f"**PDR (N={_N}):** {_rp['resultado']}, {_rp['frames']} frames, "
            f"{_rp['obrigacoes']} obrigações, {_rp['tempo']:.2f} s"]
    if _rp["resultado"] == "safe":
        _inv = _rp["testemunha"]["do"]
        _ok1 = e_modelo(_cfa, _rp["testemunha"])
        _ok2 = e_invariante(_S, inv_de_inteiros(_inv, _N))
        _txt.append(f"Invariante do PDR em `do` (dimensão {tamanho(_inv)} nós):\n"
                    f"```\n{_corta(_inv)}\n```\n"
                    f"`e_modelo`: {_ok1}   `e_invariante`: {_ok2}")
    _txt.append(f"**Interpolantes (N={_N}):** {_ri['resultado']}, (n,m)={_ri['nm']}, "
                f"{_ri['iteracoes']} interpolantes, {_ri['tempo']:.2f} s")
    if _ri["resultado"] == "safe":
        _f = _ri["invariante"]
        _ok3 = e_invariante(_S, lambda S_, X, f=_f: inst(f, S_, X))
        _txt.append(f"Invariante (dimensão {tamanho(_f)} nós):\n"
                    f"```\n{_corta(_f)}\n```\n`e_invariante`: {_ok3}")
    mo.md("\n\n".join(_txt))
    return


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito e o que se observa (alínea 3, execução)

    Para $N=3$ corre-se o PDR e o algoritmo de interpolantes sobre o sistema seguro, mostra-se o
    invariante que cada um encontrou e **verifica-se de forma independente**:

    * `e_modelo` (de `pdr_lia.py`) confirma que o resultado do PDR é um modelo das CHCs;
    * `e_invariante` faz os três testes de insatisfazibilidade sobre o SFOTS booleano. Deve dar
      `True` nos três.

    Os invariantes obtidos pelos algoritmos são tipicamente mais **complicados** que o argumento
    informal ("há um só testemunho"): são conjunções de lemas, ou uma disjunção de
    interpolantes. Mas todos têm de implicar a exclusão mútua, e é isso que se verificou.
    Se o PDR der `unknown`, atingiu os limites de passos (ver a nota técnica de escala do enunciado).
    """)
    return


@app.cell
def _(anel, anel_cfa, bmc, corre_pdr, itp_mc, referencia):
    _N = 3
    _S = anel(_N, True)
    _, _cfa = anel_cfa(_N, True)
    _rp = corre_pdr(_cfa)
    _ri = itp_mc(_S)
    _txt = [f"**Referência (BFS), N={_N}, com regeneração:** "
            f"{'seguro' if referencia(_N, True)[0] else 'INSEGURO'}",
            f"**PDR:** {_rp['resultado']}"
            + (f", caminho `{' → '.join(_rp['testemunha'])}`"
               if _rp['resultado'] == 'unsafe' else ""),
            f"**Interpolantes:** {_ri['resultado']}, (n,m)={_ri['nm']}",
            f"**BMC:** traço de erro com {len(bmc(_S, 8)) - 1} passos (ver acima)"]
    mo.md("\n\n".join(_txt))
    return


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito e o que se observa (alínea 4)

    Repete-se a verificação com `regenera=True`. Os **dois algoritmos devem detetar a
    insegurança**: o PDR devolve um caminho até `error` e o algoritmo de interpolantes devolve
    `unsafe` com o par $(n,m)$ em que o encontrou. O traço de erro concreto, passo a passo,
    é o do BMC (célula anterior).

    A regra *regenerar* quebra a invariante "há exatamente um testemunho": um processo à espera
    e sem testemunho cria um testemunho novo, e passa a ser possível haver dois processos em
    `C` ao mesmo tempo.
    """)
    return


# ---------------------------------------------------------------------------
# 5. Comparação
# ---------------------------------------------------------------------------
@app.cell
def _(anel, anel_cfa, corre_pdr, e_invariante, e_modelo, inst, inv_de_inteiros,
      itp_mc, referencia, spacer_pdr, tamanho):
    def avalia(N, regenera, max_passos=400, timeout_ms=20000):
        """Corre PDR, interpolantes e Spacer para um N e uma variante, compara com a
        pesquisa em largura e verifica os invariantes. Devolve uma linha da tabela."""
        seguro_ref, nest, dist = referencia(N, regenera)
        ref = "safe" if seguro_ref else "unsafe"
        S = anel(N, regenera)
        _, cfa = anel_cfa(N, regenera)
        linha = {"N": N, "variante": "regenera" if regenera else "normal",
                 "referência": ref}
        verificados = []

        rp = corre_pdr(cfa, max_passos=max_passos)
        linha["PDR"] = rp["resultado"]
        linha["PDR s"] = round(rp["tempo"], 2)
        linha["PDR iter"] = f"{rp['frames']} frames / {rp['obrigacoes']} obrig."
        linha["PDR dim"] = None
        if rp["resultado"] == "safe":
            inv = rp["testemunha"]["do"]
            linha["PDR dim"] = tamanho(inv)
            verificados.append(e_modelo(cfa, rp["testemunha"])
                               and e_invariante(S, inv_de_inteiros(inv, N))[0])

        try:
            ri = itp_mc(S)
        except RuntimeError:
            ri = {"resultado": "unknown", "invariante": None, "nm": None,
                  "iteracoes": None, "tempo": float("nan")}
        linha["ITP"] = ri["resultado"]
        linha["ITP s"] = round(ri["tempo"], 2)
        linha["ITP iter"] = f"(n,m)={ri['nm']} / {ri['iteracoes']} itp."
        linha["ITP dim"] = None
        if ri["resultado"] == "safe":
            f = ri["invariante"]
            linha["ITP dim"] = tamanho(f)
            verificados.append(e_invariante(S, lambda S_, X, f=f: inst(f, S_, X))[0])

        t0 = time.time()
        res_sp, inv_sp = spacer_pdr(cfa, timeout_ms)
        linha["Spacer"] = {"sat": "safe", "unsat": "unsafe"}.get(res_sp, "unknown")
        linha["Spacer s"] = round(time.time() - t0, 2)
        linha["Spacer dim"] = None
        if inv_sp:
            linha["Spacer dim"] = tamanho(inv_sp["do"])
            verificados.append(e_modelo(cfa, inv_sp))

        decididos = [linha[k] for k in ("PDR", "ITP", "Spacer") if linha[k] != "unknown"]
        linha["acordo"] = all(r == ref for r in decididos)
        linha["invariantes ok"] = all(verificados)
        return linha

    return (avalia,)


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que foi feito (alínea 5, função de avaliação)

    `avalia(N, regenera)` corre os três algoritmos para um $N$ e uma variante e devolve **uma linha
    da tabela** com, para cada um:

    * o **resultado** (`safe`, `unsafe` ou `unknown`);
    * o **tempo**;
    * o número de **iterações** (frames e obrigações no PDR; o par $(n,m)$ e o número de
      interpolantes no algoritmo de interpolantes; o Spacer não expõe iterações);
    * a **dimensão do invariante** (nós da fórmula).

    Compara ainda cada resultado com a pesquisa em largura (coluna `acordo`) e verifica **todos os
    invariantes devolvidos** com `e_modelo` ou `e_invariante` (coluna `invariantes ok`).
    """)
    return


@app.cell
def _(avalia):
    N_MAX = 4          # aumentar com cuidado: o PDR didático demora a partir de N=5
    linhas = [avalia(_N, _reg) for _N in range(2, N_MAX + 1) for _reg in (False, True)]
    assert all(_l["acordo"] for _l in linhas), "os algoritmos não concordam com a referência"
    assert all(_l["invariantes ok"] for _l in linhas), "algum invariante não passou"

    def _tab(titulo, colunas):
        def cel(v):
            return "—" if v is None else str(v)
        cab = "| " + " | ".join(colunas) + " |\n|" + "---|" * len(colunas) + "\n"
        corpo = "".join("| " + " | ".join(cel(_l[c]) for c in colunas) + " |\n"
                        for _l in linhas)
        return f"**{titulo}**\n\n{cab}{corpo}"

    mo.md("\n\n".join([
        _tab("Resultados", ["N", "variante", "referência", "PDR", "ITP", "Spacer",
                            "acordo", "invariantes ok"]),
        _tab("Tempos (s)", ["N", "variante", "PDR s", "ITP s", "Spacer s"]),
        _tab("Iterações e dimensão do invariante",
             ["N", "variante", "PDR iter", "PDR dim", "ITP iter", "ITP dim", "Spacer dim"]),
    ]))
    return N_MAX, linhas


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### O que se observa (alínea 5, tabela)

    A tabela cobre $N=2,\dots,$`N_MAX`, na versão segura (`normal`) e na variante com `regenera`.
    As duas asserções do código garantem que:

    * **os três algoritmos concordam entre si e com a pesquisa em largura** em todos os casos
      em que deram resposta (`unknown` não conta);
    * **todo o invariante devolvido passou na verificação independente.**

    Pontos a comentar no relatório depois de ver os números:

    * o tempo do PDR didático cresce depressa com $N$, e é aí que fica o limite da comparação
      (o enunciado avisa que isto acontece a partir de $N=5$);
    * o Spacer costuma ser muito mais rápido que o PDR didático, por usar interpolação e
      heurísticas globais;
    * a dimensão do invariante cresce com $N$; o invariante "à mão" (bónus) tem tamanho linear
      em $N$, e convém compará-lo com os dos algoritmos;
    * nas variantes inseguras não há invariante: a coluna de dimensão fica vazia e o que conta é o
      tempo até ao contra-exemplo.
    """)
    return


# ---------------------------------------------------------------------------
# Bónus
# ---------------------------------------------------------------------------
@app.cell
def _(anel, e_invariante, k_inducao):
    def inv_manual(S, X):
        """Invariante à mão: exatamente um testemunho e (c_i → t_i)."""
        N = S.N
        return And(PbEq([(X['t'][i], 1) for i in range(N)], 1),
                   And([Implies(X['c'][i], X['t'][i]) for i in range(N)]))

    _linhas = []
    for _N in (2, 3, 4, 5):
        _ok, _res = e_invariante(anel(_N), inv_manual)
        _linhas.append(f"N={_N}: invariante manual indutivo e seguro? {_ok}  {_res}")
    for _k in (1, 2):
        _r = k_inducao(anel(4), _k, inv_manual)
        _linhas.append(f"k-indução reforçada, N=4, k={_k}: base={_r['base']} passo={_r['passo']}")
    mo.md("```\n" + "\n".join(_linhas) + "\n```")
    return (inv_manual,)


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Bónus: invariante à mão e $k$-indução reforçada

    O argumento informal do enunciado ("só há um testemunho, e quem está na secção crítica tem-no")
    escreve-se como o invariante

    $$\mathsf{inv}\;\equiv\;\Big(\sum_i t_i = 1\Big)\;\land\;\bigwedge_i (c_i\to t_i).$$

    * **É indutivo.** `sair` e `passar` movem o único testemunho; quem o recebe não estava na
      secção crítica (porque $c_j\to t_j$ e $t_j$ era falso), e `entrar` só acontece com o
      testemunho. `e_invariante` confirma-o para vários $N$.
    * **Exclui o erro.** Dois processos em `C` teriam dois testemunhos, o que contradiz
      $\sum_i t_i=1$.
    * **A $k$-indução passa a funcionar** com $k=1$ quando se reforça a propriedade com `inv`,
      porque os contra-exemplos da alínea 2 (estados com dois testemunhos, ou com um processo em
      `C` sem testemunho) deixam de ser estados possíveis.

    Compara-se este invariante, pequeno e legível, com os que o PDR e os interpolantes encontram
    na tabela da alínea 5.
    """)
    return


if __name__ == "__main__":
    app.run()
