-- Prove2me | Theorems.Thm_FreeOrderEPTAS_Supplement_theorem_1_4
-- name    : FreeOrderEPTAS.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:42:54.713548+00:00
-- url     : https://prove2.me/theorems/12a2b74f-0251-56a9-8728-e9b28c7f0437
-- title:
--   Theorem 1.4 — EPTAS for Pandora's Box with Commitment
-- statement:
--   There exist a function $t$ and a universal exponent $d$ such that the following holds. For every $\varepsilon>0$, every instance $(X,c)$ of Pandora's Box with Commitment with $n$ boxes, every LP solver and every dependent-rounding procedure with properties (P1)–(P3), the algorithm `pandoraEPTAS` (the reduction of Theorem 6.1 run with the Free-Order Prophets algorithm of Theorem 3.1), which accesses $X$ only through the oracle $\mathbb E[\max\{X_i,v\}]$ and reads Weitzman's indices,
--
--   1. returns, with probability at least $1/2$, a solution with
--   $$\mathbb E\Big[X_{\sigma(\tau)}-\sum_{t\le\tau}c_{\sigma(t)}\Big]\ \ge\ (1-\varepsilon)\cdot\mathrm{OPT}(X,c);$$
--   2. on every outcome, has counted cost at most $t(\lceil1/\varepsilon\rceil)\cdot(n+1)^d$, each query of the $Y$-oracle being charged one $X$-oracle query and 5 operations;
--   3. hands every LP and rounding instance of size at most $t(\lceil1/\varepsilon\rceil)\cdot(n+1)$ to its subroutines.
--
--   This is an efficient polynomial-time approximation scheme: the exponent of $n$ does not depend on $\varepsilon$.
--
--   Differences from the source:
--   - reading: there exists an EPTAS → the form of Theorem 3.1 for the explicit program pandoraEPTAS: ∃ t d before ∀ ε > 0, success probability ≥ 1/2, counted cost ≤ t(⌈1/ε⌉)(n + 1)^d and LP/rounding sizes ≤ t(⌈1/ε⌉)(n + 1) on every outcome, for every valid LP solver and rounding; reason: the published goal's reading of Theorem 3.1 (paper.md items 6, 7); Theorem 1.4 is derived from it and Theorem 6.1
--   - encoding: the Y-oracle used by the Free-Order Prophets algorithm costs one X-oracle query and O(1) operations per query → the bound is on r.2.total + 5·r.2.oracle; reason: the published freeOrder charges each Y-oracle query as one oracle call; the extra 5 operations per query (callY) are added explicitly
--   - reading: κ_i, "the unique solution to E[(X_i − κ_i)^+] = c_i", with no method of computing it → the program receives κ as an input and reads κ_i at one counted operation per access; reason: κ_i is not exactly computable from E[max{X_i, v}] in finitely many real operations; the paper treats it as available
--   - encoding: Y_i = min{X_i, κ_i} → Y_i = max{min{X_i, κ_i}, 0}, and Y_i = X_i for κ_i = ∞; reason: the base instance requires non-negative values; the clip changes Y_i only when κ_i < 0 (c_i > E[X_i]), where Y_i is a.s. the constant κ_i < 0 resp. 0, and neither ever raises a stopping value
--   - reading: a solution is a probing permutation σ and a stopping rule τ (p.30), and the proofs of Claims 6.2–6.3 skip boxes the policy does not probe → a solution is either the empty solution (probe no box, utility 0) or a pair (σ, τ); a rule that never stops selects nothing and pays all n costs; reason: skipping every box must be a solution: if the only solutions were pairs (σ, τ), each probes at least one box, and for n = 1, X_1 = 0, c_1 = 1 every solution has utility −1 while V_Y(σ) = 0, so Claim 6.3 would be false and Theorem 6.1 false for α < 1
--   - generalization: all random variables are continuous (footnote 1, p.31, an assumption of the proof) → every non-negative integrable law; reason: κ_i exists and is unique for every integrable law with c_i > 0, and the per-box identities of both claims need no continuity; the continuous case is a special case
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Theorem 1.4, p.5

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Supplement_pandoraEPTAS
import Definitions.Def_FreeOrderEPTAS_orc

namespace FreeOrderEPTAS.Supplement

/-- Theorem 1.4 (arXiv:2007.13121v3, p.5): there exists an EPTAS for Pandora's Box with Commitment,
in the form of Theorem 3.1, about the program `pandoraEPTAS` (the reduction of Theorem 6.1 run with
the published `freeOrder`), which reaches `X` only through its counted oracle `E[max{X_i, v}]` and
reads Weitzman's indices `κ`.

There are `t` and a universal `d` such that, for every `ε > 0`, every instance with `n` boxes, every
LP solver and every rounding with (P1)–(P3): with probability at least `1/2` the returned solution has
expected utility at least `(1 − ε) · OPT(X, c)`, and on every outcome the counted cost, with each
query of the `Y`-oracle made by `freeOrder` charged a further 5 operations, is at most
`t(⌈1/ε⌉) (n + 1)^d`, and every LP or rounding instance has size at most `t(⌈1/ε⌉) (n + 1)`. -/
theorem theorem_1_4 :
    ∃ (t : ℕ → ℕ) (d : ℕ), ∀ (ε : ℝ), 0 < ε → ∀ (n : ℕ) (P : PandoraInstance n) (lp : LPSolver)
      (rnd : Rounding), IsLPSolver lp → IsDependentRounding rnd →
      (1 / 2 : ℝ) ≤ pr ((pandoraEPTAS ε (orc P.X) (kappa P) P.c lp rnd).run 0)
          {r | (1 - ε) * pandoraOPT P ≤ pandoraValue P r.1} ∧
      ∀ r ∈ ((pandoraEPTAS ε (orc P.X) (kappa P) P.c lp rnd).run 0).support,
        r.2.total + 5 * r.2.oracle ≤ t ⌈1 / ε⌉₊ * (n + 1) ^ d ∧
          r.2.maxSize ≤ t ⌈1 / ε⌉₊ * (n + 1) := by sorry

end FreeOrderEPTAS.Supplement
