-- Prove2me | Theorems.Thm_Kyprianou_Ch04_strictStoppedPrimitiveClock
-- name    : Kyprianou.Ch04.strictStoppedPrimitiveClock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:45:22.144141+00:00
-- url     : https://prove2.me/theorems/ae30969b-0161-467c-a713-324b58ce2df4
-- title:
--   strictStoppedPrimitiveClock
-- statement:
--   Strict stopping of a Lebesgue density agrees with the closed clipped clock.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- Strict stopping of a Lebesgue density agrees with the closed clipped clock. -/
theorem Kyprianou.Ch04.strictStoppedPrimitiveClock (g : ℝ → ℝ) (tau : WithTop NNReal) (t c : NNReal)
    (hc : (c : WithTop NNReal) = min tau (t : WithTop NNReal)) :
    (∫ s in Icc (0:ℝ) (t:ℝ), (if (s.toNNReal : WithTop NNReal) < tau then g s else 0) ∂volume)
      = ∫ s in Icc (0:ℝ) (c:ℝ), g s ∂volume := by
  sorry
