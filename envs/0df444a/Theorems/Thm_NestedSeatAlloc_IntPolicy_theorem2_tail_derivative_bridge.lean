-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_tail_derivative_bridge
-- name    : NestedSeatAlloc.IntPolicy.theorem2_tail_derivative_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T13:44:01.460773+00:00
-- url     : https://prove2.me/theorems/64489994-700a-4d19-877a-cf626eca8481
-- title:
--   Theorem 2 tail witness from the one-class derivative formula
-- statement:
--   If the one-class expected-revenue derivative formula is available and some positive seat level has derivative below the next fare, then the strict positive tail-bound witness follows.
-- source:
--   Source-faithful witness-extraction bridge for equation (27): instantiate the right derivative formula at the positive tail point.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem2_tail_derivative_bridge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hderiv : ∀ s, 0 ≤ s →
      HasDerivWithinAt (expRevenue P X f p 1)
        (f 1 * P.real {ω | s < X 1 ω}) (Set.Ici s) s)
    (htail : ∃ s, 0 < s ∧ f 1 * P.real {ω | s < X 1 ω} < f 2) :
    ∃ s, 0 < s ∧ ∃ r,
      HasDerivWithinAt (expRevenue P X f p 1) r (Set.Ici s) s ∧ r < f 2 := by sorry

end NestedSeatAlloc.IntPolicy
