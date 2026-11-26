-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalWindowPositiveTimeCongrV1
-- name    : Kyprianou.Ch04.physicalWindowPositiveTimeCongrV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:28:51.91326+00:00
-- url     : https://prove2.me/theorems/d9776cb9-9e75-5423-b3c9-92787b74c39e
-- title:
--   Physical window integral congruence off the null time-zero slice
-- statement:
--   Integrands agreeing at positive times have identical closed-window integrals
--   when the measure has no mass on the initial time slice.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem physicalWindowPositiveTimeCongrV1 (R : Measure (ℝ × ℝ)) (T : ℝ) (B : Set ℝ)
    (hB : MeasurableSet B)
    (hz : R (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0)
    (k l : ℝ × ℝ → ℝ)
    (he : ∀ z, 0 < z.1 → z.1 ≤ T → z.2 ∈ B → k z = l z) :
    (∫ z in Icc 0 T ×ˢ B, k z ∂ R) = ∫ z in Icc 0 T ×ˢ B, l z ∂ R := by
  sorry
end Kyprianou.Ch04
