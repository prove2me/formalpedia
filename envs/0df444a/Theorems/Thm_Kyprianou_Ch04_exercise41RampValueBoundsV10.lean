-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41RampValueBoundsV10
-- name    : Kyprianou.Ch04.exercise41RampValueBoundsV10
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:38:41.459463+00:00
-- url     : https://prove2.me/theorems/13115e00-bbc4-4f11-9979-b43239878373
-- title:
--   Primitive of clipped ramp vanishes on the negative half-line and approximates positive part with error at most epsilon
-- statement:
--   Primitive of clipped ramp vanishes on the negative half-line and approximates positive part with error at most epsilon
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41RampValueBoundsV10
    (ε : ℝ) (he : 0 < ε) (x : ℝ) :
    let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
    let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
    (x ≤ 0 → p x = 0) ∧
      0 ≤ p x ∧ p x ≤ max 0 x ∧ max 0 x - ε ≤ p x := by
  sorry
