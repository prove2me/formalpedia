-- Prove2me | Theorems.Thm_NadlerCLS_holder_total
-- name    : NadlerCLS.holder_total
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:02:31.309612+00:00
-- url     : https://prove2.me/theorems/d54e34c1-d14e-4295-a868-3a73cf54ed0f
-- title:
--   Totality of $\beta$-Hölder-LocalOpt
-- statement:
--   For every fixed dimension $n\ge1$ and every fixed rational $\beta\in(0,1]$, every instance $(f,p,\delta,\lambda)$ of $\beta$-Hölder-LocalOpt on $[0,1]^n$ has a valid output (HO1), (HO2) or (HO3) at rational points.
--
--   The argument in the paper iterates $x_{t+1}=f(x_t)$: without (HO1) answers $p$ would decrease by more than $\delta$ at every step, which is impossible for a potential with values in $[0,1]$.
--
--   Differences from the source:
--   - generalization: the problems printed on $[0,1]^3$ (Definitions 1, 2, 5) → every fixed dimension $n \ge 1$, the problems on $[0,1]^n$; reason: Appendix C proves the reductions on $[0,1]^n$ (p.34: "for generality"; p.37: "works for any polynomial dimension n"); $n = 3$ is the printed case
--   - encoding: circuits with the ranges $f:[0,1]^n\to[0,1]^n$, $p:[0,1]^n\to[0,1]$ (and $P(X)\subseteq X$, $d \in [0,D]$) → raw circuit outputs clipped to these ranges with $\min/\max$; reason: Remark C.7's coordinate-wise clipping; it leaves every in-range instance unchanged
--   - encoding: answers are points of the cube, parameters rational in binary → answers are tagged rational points (`encNat` tag followed by `encVector`s); reductions are the public `CardinalMatching.SearchReduces` (polynomial-time on Cook's Turing machines, every target answer decoded); reason: p.7's computational model: rational data in binary, polynomial-time many-one reductions with a decoder for every valid solution
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Section C.1, p.31

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_holderSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Totality of β-Hölder-LocalOpt** (Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485,
Section C.1, p.31: "We claim that the problem is total"). For every `n ≥ 1` and
rational `β ∈ (0, 1]`, every β-Hölder-LocalOpt instance has a valid output (HO1)–(HO3).

**Formalization Note** Answers are rational points of the cube. -/
theorem holder_total (n : ℕ) (hn : 1 ≤ n) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    TotalSearch (holderSearch n β) := by sorry

end NadlerCLS
