-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_integral_expRevenue_mul_next_event_indicator
-- name    : NestedSeatAlloc.IntPolicy.integral_expRevenue_mul_next_event_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T20:27:39.651017+00:00
-- url     : https://prove2.me/theorems/05585a65-c923-41b0-9456-1fb483784d2c
-- title:
--   Factor lower-level revenue across the next-demand event
-- statement:
--   For independent integer-coordinate seat models, the expected lower-level revenue multiplied by an event indicator of the next demand factors as expected revenue times the event probability.
-- source:
--   This is the specific expectation-level independence bridge needed to condition the positive-index CLBI propagation step on the next demand. The source route is finite-coordinate iIndepFun between Finset.Icc 1 k and {k+1}, composed with the measurable prefix-revenue map and event indicator, followed by IndepFun.integral_fun_mul_eq_mul_integral. The fare-bound induction ensures fixed nonnegative-seat revenue is integrable under the probability measure. It does not itself establish the parent affine conclusion.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix

open Classical

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem integral_expRevenue_mul_next_event_indicator
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (hp : ∀ i, 0 ≤ p i)
    (E : Set ℝ) (hE : MeasurableSet E) :
    ∫ ω, revenue f p (fun i => X i ω) k t *
        (if X (k + 1) ω ∈ E then (1 : ℝ) else 0) ∂P =
      expRevenue P X f p k t * P.real (X (k + 1) ⁻¹' E) := by sorry

end NestedSeatAlloc.IntPolicy
