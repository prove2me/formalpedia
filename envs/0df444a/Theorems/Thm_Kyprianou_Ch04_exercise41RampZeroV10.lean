-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41RampZeroV10
-- name    : Kyprianou.Ch04.exercise41RampZeroV10
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:40:12.535899+00:00
-- url     : https://prove2.me/theorems/df7e9df7-8045-54c4-8554-55b09dde7925
-- title:
--   Clipped ramp primitive vanishes for nonpositive arguments
-- statement:
--   Clipped ramp primitive vanishes for nonpositive arguments
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41RampZeroV10
    (ε : ℝ) (he : 0 < ε) (x : ℝ) (hx : x ≤ 0) :
    let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
    let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
    p x = 0 := by
  sorry
