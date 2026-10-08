-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_theorem_2_3_i
-- name    : GenCoupling.Ergodic.theorem_2_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:47.119987+00:00
-- url     : https://prove2.me/theorems/b7f6adfb-21e0-479f-bf5b-7acb546fbe13
-- title:
--   Theorem 2.3(i), p. 8 — under A, d_N is contracting for P_t whenever r(t) ≤ 1/3 and N ≥ 2L(t)
-- statement:
--   Let $(E,\rho)$ be a Polish space, $\{P_t\}$ a Markov semigroup on $E$ and $\theta$ a premetric. Assume Assumption A holds for functions $r,L$: for all $x,y$ there is a generalized coupling $(X^{x,y},Y^{x,y})$ with $\mathrm{Law}(X^{x,y}_t)=P_t(x,\cdot)$, $d_{TV}(\mathrm{Law}(Y^{x,y}_t),P_t(y,\cdot))\le L(t)\theta(x,y)$ and $\mathsf E\theta(X^{x,y}_t,Y^{x,y}_t)\le r(t)\theta(x,y)$.
--
--   Then for any $N>0$ and $t>0$ such that
--   $$r(t)\le\tfrac13\qquad\text{and}\qquad N\ge 2L(t),$$
--   the distance-like function $d_N=N\theta(x,y)\wedge N\theta(y,x)\wedge1$ is contracting for $P_t$ in the sense of Definition 2.1: there is $\alpha<1$ with $W_{d_N}(P_t(x,\cdot),P_t(y,\cdot))\le\alpha\,d_N(x,y)$ whenever $d_N(x,y)<1$.
--
--   This is how the generalized coupling replaces the contractivity condition (2.3) of Proposition 2.1.
--
--   **Formalization Note** "Contracting" includes that $d_N$ is distance-like and bounded by 1, as in Definition 2.1. "Law$(X^{x,y})=\mathsf P_x$" is read through one-dimensional marginals (see the Setting definition).
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 8, Theorem 2.3(i)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Theorem 2.3(i), p. 8: under Assumption A, for `N > 0`, `t > 0` with `r(t) ≤ 1/3` and
`N ≥ 2L(t)`, the distance-like function `d_N` is contracting for `P_t`. -/
theorem theorem_2_3_i {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℝ≥0 → Kernel E E) (hP : IsMarkovSemigroup P)
    (θ : E → E → ℝ) (hθ : IsPremetric θ) (r L : ℝ≥0 → ℝ) (hA : AssumptionA θ P r L)
    (N : ℝ) (t : ℝ≥0) (hN : 0 < N) (ht : 0 < t) (hr : r t ≤ 1 / 3) (hL : 2 * L t ≤ N) :
    IsContracting P t (dN θ N) := by sorry

end GenCoupling.Ergodic
