-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rightContinuousZeroPrimitive
-- name    : Kyprianou.Ch04.rightContinuousZeroPrimitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:42:13.770413+00:00
-- url     : https://prove2.me/theorems/47ebe21b-b437-5e94-96d2-c38a83360ac1
-- title:
--   rightContinuousZeroPrimitive
-- statement:
--   A right-continuous time density whose primitive vanishes identically must vanish.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A right-continuous time density whose primitive vanishes identically must vanish. -/
theorem Kyprianou.Ch04.rightContinuousZeroPrimitive (g : ℝ → ℝ) (hm : Measurable g)
    (hi : ∀ t : NNReal, IntegrableOn g (Icc (0 : ℝ) (t : ℝ)) volume)
    (hr : ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt g (Ici s) s)
    (hz : ∀ t : NNReal, (∫ r in Icc (0 : ℝ) (t : ℝ), g r ∂volume) = 0) :
    ∀ s : ℝ, 0 ≤ s → g s = 0 := by
  sorry
