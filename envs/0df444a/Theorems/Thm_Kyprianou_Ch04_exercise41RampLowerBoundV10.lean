-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41RampLowerBoundV10
-- name    : Kyprianou.Ch04.exercise41RampLowerBoundV10
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:40:13.339895+00:00
-- url     : https://prove2.me/theorems/2b8c34ea-1ad0-5723-8aa2-b1d1430644e5
-- title:
--   Ramp primitive approximates identity from below with error at most epsilon beyond the transition
-- statement:
--   Ramp primitive approximates identity from below with error at most epsilon beyond the transition
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41RampLowerBoundV10
    (ε : ℝ) (he : 0 < ε) (x : ℝ) (hx : ε ≤ x) :
    let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
    let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
    x - ε ≤ p x := by
  sorry
