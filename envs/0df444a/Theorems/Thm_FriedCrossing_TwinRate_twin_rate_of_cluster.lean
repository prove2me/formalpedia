-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_twin_rate_of_cluster
-- name    : FriedCrossing.TwinRate.twin_rate_of_cluster
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:41:41.044181+00:00
-- url     : https://prove2.me/theorems/80c70707-0fa9-4d1f-9ea0-0bf7a9f1bc1d
-- title:
--   Twin Rate: twin rate of cluster
-- statement:
--   THE RATE LEMMA. From (i) C¹ cluster data a, b (trace and determinant of N, with
--   τ-derivatives a', b', all four continuous at (0,0)), (ii) a(0,0) = r₀ > 0, (iii) b(0,0) = 0:
--   on a full neighbourhood |θ| < ε, |τ| < ε the discriminant is positive, the twin branch is
--   differentiable in τ with derivative `dtwin`, and that derivative lies in [r₀/2, 2r₀].
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L189-L246
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L189-L246

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.twin_rate_of_cluster (sStar : ℝ → ℝ) (a b a' b' : ℝ → ℝ → ℝ) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hderiv_a : ∀ θ τ, HasDerivAt (a θ) (a' θ τ) τ)
    (hderiv_b : ∀ θ τ, HasDerivAt (b θ) (b' θ τ) τ)
    (hcont_a : ContinuousAt (Function.uncurry a) (0, 0))
    (hcont_b : ContinuousAt (Function.uncurry b) (0, 0))
    (hcont_a' : ContinuousAt (Function.uncurry a') (0, 0))
    (hcont_b' : ContinuousAt (Function.uncurry b') (0, 0))
    (ha0 : a 0 0 = r₀) (hb0 : b 0 0 = 0) :
    ∃ ε > 0, ∀ θ τ : ℝ, |θ| < ε → |τ| < ε →
      0 < disc (a θ τ) (b θ τ) ∧
      HasDerivAt (twin sStar a b θ) (dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ) τ ∧
      r₀ / 2 ≤ dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ ∧
      dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ ≤ 2 * r₀ := by sorry
