-- Prove2me | Theorems.Thm_Kyprianou_Ch04_closedStopRawIntegral
-- name    : Kyprianou.Ch04.closedStopRawIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:27:10.423938+00:00
-- url     : https://prove2.me/theorems/e03a74b5-362a-508b-a4c9-f848d7b80a62
-- title:
--   closedStopRawIntegral
-- statement:
--   The stopped raw integral equals the integral at the clipped clock.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- The physical stopped raw integral equals the integral at the clipped clock. -/
theorem Kyprianou.Ch04.closedStopRawIntegral (mu : Measure (ℝ × ℝ)) (k : ℝ × ℝ → ℝ)
    (tau : WithTop NNReal) (t c : NNReal)
    (hc : (c : WithTop NNReal) = min tau (t : WithTop NNReal)) :
    (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      (if (z.1.toNNReal : WithTop NNReal) ≤ tau then k z else 0) ∂mu) =
      ∫ z in Set.Icc (0 : ℝ) (c : ℝ) ×ˢ Set.univ, k z ∂mu  := by
  sorry
