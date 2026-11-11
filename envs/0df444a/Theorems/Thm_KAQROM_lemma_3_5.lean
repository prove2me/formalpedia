-- Prove2me | Theorems.Thm_KAQROM_lemma_3_5
-- name    : KAQROM.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:03.880024+00:00
-- url     : https://prove2.me/theorems/27878b55-ab42-4e57-91a1-0df4e0690b23
-- title:
--   Lemma 3.5 — random reprogramming lemma: advantage at most $2q\sqrt\varepsilon$
-- statement:
--   Let $D$ be a distinguisher in the random reprogramming game: $D$ outputs a full function $F_0:X\to Y$ and a randomized classical algorithm $C$ whose output is a partial function $R$; the challenger samples $R\leftarrow C$, sets $F_1=F_0[R]$, picks $b$, and gives $D$ quantum oracle access to $F_b$; then the oracle is removed, the coins of $C$ are revealed, and $D$ outputs a bit. Let
--   $$
--   \varepsilon=\max_{x\in X}\Pr_{R\leftarrow C}[x\in\mathrm{Dom}(R)].
--   $$
--   If $D$ makes at most $q$ challenge-oracle queries, then
--   $$
--   \bigl|\Pr[D\text{ outputs }1\mid b=1]-\Pr[D\text{ outputs }1\mid b=0]\bigr|\le 2q\sqrt\varepsilon .
--   $$
--
--   This is the lemma of Alagic et al. and Katz–Sela, used in Lemmas 5.15 and 5.16 to swap the oracle used by the final stages.
--
--   **Formalization Note** The statement is for each fixed first message $(F_0,C)$ of $D$ and each initial state; a randomized choice follows by averaging. Any $\varepsilon$ bounding every $\Pr[x\in\mathrm{Dom}(R)]$ may be used.
--
--   Differences from the source:
--   - encoding: a security parameter λ with inputs $1^\lambda$ → one fixed λ, $1^\lambda$ arguments dropped; reason: every statement of §5.2 is at one fixed λ with explicit constants
--   - generalization: $X=\{0,1\}^{n(\lambda)}$, $Y=\{0,1\}^{\ell(\lambda)}$ with $\ell(\lambda)\ge1$ → any finite type $X$ and any $\ell\in\mathbb N$, including $\ell=0$ (with $Y=\{0,1\}^\ell$ kept as bit strings, XOR as addition in $\mathbb Z_2^\ell$); reason: $n(\lambda)$, $\ell(\lambda)$ enter only through the sets $X$, $Y$ and no argument uses $\ell\ge1$; $X=\{0,1\}^n$, $\ell\ge1$ is an instance
--   - encoding: quantum oracle algorithms making at most $q$ queries, alternating oracle-independent operations with $U_H$ → exactly $q$ query rounds interleaved with arbitrary channels (Kraus families), then a measurement; reason: a query on the response state $|+\rangle^{\otimes\ell}$ is idle, so any algorithm pads to exactly $q$; parties are computationally unbounded (Stinespring)
--   - encoding: $D$ outputs $(F_0,C)$, possibly at random → the bound for every fixed $(F_0,C)$ and initial state of $D$; reason: the randomized case is an average of fixed cases, each bounded by $2q\sqrt\varepsilon$
--   - encoding: $\varepsilon=\max_x\Pr_{R\leftarrow C}[x\in\mathrm{Dom}(R)]$ → any $\varepsilon$ with $\Pr_{R\leftarrow C}[x\in\mathrm{Dom}(R)]\le\varepsilon$ for all $x$; reason: the bound is monotone in $\varepsilon$; the maximum is an instance
--   - encoding: a randomized classical algorithm $C$ whose coins are revealed → a discrete coin distribution on any type with an output map to partial functions; reason: this is a randomized classical algorithm; its coins are what is revealed
--   - encoding: $D$ outputs a bit after the coins are revealed → a two-outcome measurement chosen by the revealed coins; reason: $D$'s final processing may depend on the coins
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 3.5, p.19 ([KS24, Lemma 3], [ABKM22, Lemma 3])

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_reprogGameProb

namespace KAQROM

/-- **Lemma 3.5 (Random reprogramming lemma).** In the game of `reprogGameProb`, let
`ε ≥ max_x Pr_{R←C}[x ∈ Dom(R)]`. If `D` makes at most `q` challenge-oracle queries, then
`|Pr[D outputs 1 | b = 1] − Pr[D outputs 1 | b = 0]| ≤ 2q√ε`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 3.5, p.19 ([KS24, Lemma 3], [ABKM22, Lemma 3]).

**Formalization Note.** The distinguisher's first message `(F₀, C)` is fixed (the bound for a
randomized choice follows by averaging); `C` is a discrete coin distribution `p` (any coin type)
with an output map `out`; `D`'s state is any density operator; its `q` query rounds are exactly `q`
(idle queries pad); its final measurement depends on the revealed coins. `ε` is any upper bound
on the maximum (the bound is monotone in `ε`). -/
theorem lemma_3_5 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {C Rin W Rout ι : Type}
    [Fintype Rin] [Fintype W] [Fintype Rout] [Fintype ι] [DecidableEq Rin]
    [DecidableEq W] [DecidableEq Rout] {q : ℕ} (F0 : Oracle X ℓ) (p : PMF C)
    (out : C → PartialOracle X ℓ)
    (ρ : Matrix Rin Rin ℂ) (hρ : WildeQIT.IsDensityOperator ρ)
    (A : QAlg X ℓ Rin W Rout Unit ι q) (meas : C → Instrument Bool Rout Unit ι) (ε : ℝ)
    (hε : ∀ x, reprogMass p out x ≤ ε) :
    |reprogGameProb F0 p out ρ A meas true - reprogGameProb F0 p out ρ A meas false| ≤
      2 * q * Real.sqrt ε := by sorry

end KAQROM
