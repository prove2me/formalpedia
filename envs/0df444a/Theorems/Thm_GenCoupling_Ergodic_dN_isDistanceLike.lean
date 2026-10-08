-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_dN_isDistanceLike
-- name    : GenCoupling.Ergodic.dN_isDistanceLike
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:54.800979+00:00
-- url     : https://prove2.me/theorems/dab47481-b2a1-4f78-96b6-1b99a3bc0cde
-- title:
--   (2.6), p. 7 — d_N = Nθ(x,y) ∧ Nθ(y,x) ∧ 1 is distance-like, bounded by 1, and d_N ≤ Nθ
-- statement:
--   Let $(E,\rho)$ be a Polish space and $\theta$ a premetric on $E$: a lower semicontinuous function $\theta:E\times E\to\mathbb R_+$ with $\theta(x,y)=0\iff x=y$. For $N>0$ put
--   $$d_N(x,y)=N\theta(x,y)\wedge N\theta(y,x)\wedge 1.$$
--   Then $d_N$ is distance-like (nonnegative, symmetric, lower semicontinuous, vanishing exactly on the diagonal), $d_N\le 1$, and $d_N(x,y)\le N\theta(x,y)$ for all $x,y\in E$.
--
--   The paper introduces $d_N$ in (2.6) as "the following distance-like function" and uses $d_N\le N\theta$ on p. 9; $d_N$ is the distance for which Theorem 2.3 verifies contractivity and smallness.
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 7, (2.6); p. 9, "the fact that d_N ⩽ Nθ"

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- (2.6), p. 7: for a premetric `θ` and `N > 0`, `d_N = Nθ(x,y) ∧ Nθ(y,x) ∧ 1` is
distance-like, bounded by `1`, and `d_N ≤ Nθ`. -/
theorem dN_isDistanceLike {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (θ : E → E → ℝ) (hθ : IsPremetric θ) (N : ℝ) (hN : 0 < N) :
    IsDistanceLike (dN θ N) ∧ (∀ x y, dN θ N x y ≤ 1) ∧ ∀ x y, dN θ N x y ≤ N * θ x y := by sorry

end GenCoupling.Ergodic
