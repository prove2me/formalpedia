-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41RampPositiveBoundsV10
-- name    : Kyprianou.Ch04.exercise41RampPositiveBoundsV10
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:40:12.90511+00:00
-- url     : https://prove2.me/theorems/e39fd4b4-36c2-5255-b4a6-3575a0903dbc
-- title:
--   Nonnegative ramp primitive is between zero and its nonnegative argument
-- statement:
--   Nonnegative ramp primitive is between zero and its nonnegative argument
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41RampPositiveBoundsV10
    (ε : ℝ) (x : ℝ) (hx : 0 ≤ x) :
    let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
    let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
    0 ≤ p x ∧ p x ≤ x := by
  sorry
