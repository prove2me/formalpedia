-- Prove2me | Theorems.Thm_NadlerCLS_remark_C_7
-- name    : NadlerCLS.remark_C_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:06:19.015115+00:00
-- url     : https://prove2.me/theorems/742042c6-0edc-42c1-8df4-49a10a4cc552
-- title:
--   Remark C.7 — totality of $\beta$-Projected-Nadler without the metric promise
-- statement:
--   For every fixed dimension $n\ge1$ and every fixed rational $\beta\in(0,1]$, every instance of $\beta$-Projected-Nadler on $[0,1]^n$ that satisfies the numerical condition $0<\varepsilon_2<(1-k)\varepsilon_1$ (with the ranges $P(X)\subseteq X$ and $d(X,X)\subseteq[0,D]$ enforced by clipping) has a valid output (N1)–(N4), whether or not $d$ is a metric and $(X,d)$ complete.
--
--   Totality is what makes the problem a TFNP search problem; the metric promise is what connects its answers to Nadler's theorem.
--
--   Differences from the source:
--   - generalization: the problems printed on $[0,1]^3$ (Definitions 1, 2, 5) → every fixed dimension $n \ge 1$, the problems on $[0,1]^n$; reason: Appendix C proves the reductions on $[0,1]^n$ (p.34: "for generality"; p.37: "works for any polynomial dimension n"); $n = 3$ is the printed case
--   - encoding: circuits with the ranges $f:[0,1]^n\to[0,1]^n$, $p:[0,1]^n\to[0,1]$ (and $P(X)\subseteq X$, $d \in [0,D]$) → raw circuit outputs clipped to these ranges with $\min/\max$; reason: Remark C.7's coordinate-wise clipping; it leaves every in-range instance unchanged
--   - encoding: answers are points of the cube, parameters rational in binary → answers are tagged rational points (`encNat` tag followed by `encVector`s); reductions are the public `CardinalMatching.SearchReduces` (polynomial-time on Cook's Turing machines, every target answer decoded); reason: p.7's computational model: rational data in binary, polynomial-time many-one reductions with a decoder for every valid solution
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Remark C.7, p.38

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_pnSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Remark C.7: totality of β-Projected-Nadler without the metric promise** (Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485,
Remark C.7, p.38: "subject to the numerical condition 0 < ε2 < (1 − k)ε1 and the
(enforced) range conditions P(X) ⊆ X and d(X, X) ⊆ [0, D], the membership reduction and the totality
of β-PROJECTED-NADLER hold for arbitrary well-behaved circuits"). For every `n ≥ 1` and rational
`β ∈ (0, 1]`, every β-Projected-Nadler instance in the input format (no metric or completeness
promise) has a valid output (N1)–(N4).

**Formalization Note** Ranges are enforced by the clipping in `PNInstance`; answers are rational
points. -/
theorem remark_C_7 (n : ℕ) (hn : 1 ≤ n) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    TotalSearch (pnSearch n β) := by sorry

end NadlerCLS
