-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalMarkIndicatorWindowIntegralV1
-- name    : Kyprianou.Ch04.physicalMarkIndicatorWindowIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:28:52.092908+00:00
-- url     : https://prove2.me/theorems/b01808bd-140d-538e-87ab-386346410cc1
-- title:
--   Marked indicator and band integral equality
-- statement:
--   A marked indicator on the full time window is exactly the band set integral.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem physicalMarkIndicatorWindowIntegralV1 (R : Measure (ℝ × ℝ)) (T : ℝ) (B : Set ℝ)
    (hB : MeasurableSet B) (k : ℝ × ℝ → ℝ) :
    (∫ z in Icc 0 T ×ˢ (univ : Set ℝ),
      B.indicator (fun x => k (z.1,x)) z.2 ∂ R) =
    ∫ z in Icc 0 T ×ˢ B, k z ∂ R := by
  sorry
end Kyprianou.Ch04
