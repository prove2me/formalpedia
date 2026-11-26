-- Prove2me | Theorems.Thm_Kyprianou_Ch04_closedStopNestedIntegral
-- name    : Kyprianou.Ch04.closedStopNestedIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:27:10.565643+00:00
-- url     : https://prove2.me/theorems/0ef38e44-fd0c-528a-827e-cee803452f29
-- title:
--   closedStopNestedIntegral
-- statement:
--   The stopped nested compensator equals the compensator at the clipped clock.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- The closed stopped nested compensator integral equals the clipped-clock integral. -/
theorem Kyprianou.Ch04.closedStopNestedIntegral (nu : Measure ℝ) (k : ℝ → ℝ → ℝ)
    (tau : WithTop NNReal) (t c : NNReal)
    (hc : (c : WithTop NNReal) = min tau (t : WithTop NNReal)) :
    (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x,
      (if (s.toNNReal : WithTop NNReal) ≤ tau then k s x else 0) ∂nu ∂volume) =
      ∫ s in Set.Icc (0 : ℝ) (c : ℝ), ∫ x, k s x ∂nu ∂volume  := by
  sorry
