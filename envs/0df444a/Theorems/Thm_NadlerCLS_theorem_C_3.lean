-- Prove2me | Theorems.Thm_NadlerCLS_theorem_C_3
-- name    : NadlerCLS.theorem_C_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T22:02:57.611497+00:00
-- url     : https://prove2.me/theorems/446cdd49-0a86-49de-bca9-41f43fd3fc60
-- title:
--   Theorem C.3 — Continuous-LocalOpt reduces to $\beta$-Hölder-LocalOpt
-- statement:
--   For every fixed dimension $n\ge1$ and every fixed rational $\beta\in(0,1]$ there is a polynomial-time many-one reduction
--   $$ \text{Continuous-LocalOpt}\ \le_p\ \beta\text{-Hölder-LocalOpt} $$
--   on $[0,1]^n$. In the paper the target instance is $(f,p,\delta,n\lambda)$.
--
--   Differences from the source:
--   - generalization: the problems printed on $[0,1]^3$ (Definitions 1, 2, 5) → every fixed dimension $n \ge 1$, the problems on $[0,1]^n$; reason: Appendix C proves the reductions on $[0,1]^n$ (p.34: "for generality"; p.37: "works for any polynomial dimension n"); $n = 3$ is the printed case
--   - encoding: circuits with the ranges $f:[0,1]^n\to[0,1]^n$, $p:[0,1]^n\to[0,1]$ (and $P(X)\subseteq X$, $d \in [0,D]$) → raw circuit outputs clipped to these ranges with $\min/\max$; reason: Remark C.7's coordinate-wise clipping; it leaves every in-range instance unchanged
--   - encoding: answers are points of the cube, parameters rational in binary → answers are tagged rational points (`encNat` tag followed by `encVector`s); reductions are the public `CardinalMatching.SearchReduces` (polynomial-time on Cook's Turing machines, every target answer decoded); reason: p.7's computational model: rational data in binary, polynomial-time many-one reductions with a decoder for every valid solution
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Theorem C.3, p.36

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_coSearch
import Definitions.Def_NadlerCLS_holderSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Theorem C.3: Continuous-LocalOpt reduces to β-Hölder-LocalOpt** (Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485,
Theorem C.3, p.36: "For every fixed rational β ∈ (0, 1], there is a polynomial-time
reduction from CONTINUOUS-LOCALOPT to β-HÖLDER-LOCALOPT"). For every `n ≥ 1` and rational
`β ∈ (0, 1]`, Continuous-LocalOpt on `[0, 1]ⁿ` reduces to β-Hölder-LocalOpt on `[0, 1]ⁿ` by a
polynomial-time search reduction.

**Formalization Note** Printed for Definitions 2 and 5, proved on `[0, 1]ⁿ` (p.37). -/
theorem theorem_C_3 (n : ℕ) (hn : 1 ≤ n) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    SearchReduces (coSearch n) (holderSearch n β) := by sorry

end NadlerCLS
