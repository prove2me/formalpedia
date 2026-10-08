-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_expRevenue_one_right_derivative
-- name    : NestedSeatAlloc.IntPolicy.expRevenue_one_right_derivative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T20:50:23.396199+00:00
-- url     : https://prove2.me/theorems/f181dfe1-72dd-485a-90a4-331ac8998977
-- title:
--   Equation (27) right derivative for one-class expected revenue
-- statement:
--   For an integer-valued one-class demand under the seat model, the right derivative of expected one-class revenue at every nonnegative seat level is fare one times the strict demand tail probability.
-- source:
--   Source-faithful equation-(27) integrated derivative obligation for the one-class expected revenue. The pointwise truncation derivative is the strict indicator tail; the theorem isolates the remaining one-sided differentiation-under-the-integral argument for the exact theorem2 base-tail proof.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem expRevenue_one_right_derivative
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hf1 : 0 ≤ f 1) :
    ∀ s, 0 ≤ s →
      HasDerivWithinAt (expRevenue P X f p 1)
        (f 1 * P.real {ω | s < X 1 ω}) (Set.Ici s) s := by sorry

end NestedSeatAlloc.IntPolicy
