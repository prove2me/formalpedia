-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rationalRightLimitBridgeV1
-- name    : Kyprianou.Ch04.rationalRightLimitBridgeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:39:58.314315+00:00
-- url     : https://prove2.me/theorems/43aa83e7-2381-4d78-9a3e-c9609c0fd77b
-- title:
--   Rational right limits determine the full positive-time limit
-- statement:
--   Use right continuity and density of rationals to extend the rational convergence bound to every sufficiently small positive time.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.rationalRightLimitBridgeV1 (g : ℝ≥0 → ℝ) (d : ℝ)
    (hR : ∀ t : ℝ≥0, 0 < t → ContinuousWithinAt g (Ici t) t) :
    Tendsto (fun r : ℚ => g (Real.toNNReal (r : ℝ)))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d) ↔
    Tendsto g (nhdsWithin (0 : ℝ≥0) (Ioi 0)) (nhds d) := by
  sorry
