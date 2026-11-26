-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SmoothJoinValueV11
-- name    : Kyprianou.Ch04.exercise41SmoothJoinValueV11
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:45:49.070404+00:00
-- url     : https://prove2.me/theorems/9bacce54-2dba-5d31-b781-f0cdcf10607a
-- title:
--   Pointwise convergence of the two smooth compositions to the joined continuous function
-- statement:
--   Pointwise convergence of the two smooth compositions to the joined continuous function
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41SmoothJoinValueV11
    (fLeft fRight : ℝ → ℝ)
    (hL : ContDiff ℝ 1 fLeft) (hR : ContDiff ℝ 1 fRight)
    (p : ℕ → ℝ → ℝ)
    (hP : ∀ x, Tendsto (fun n => p n x) atTop (𝓝 (max 0 x)))
    (x : ℝ) :
    let g := fun n (x : ℝ) => fLeft (-p n (-x)) - fLeft 0 +
      fRight (p n x) - fRight 0
    Tendsto (fun n => g n x) atTop (𝓝
      (if x < 0 then fLeft x - fLeft 0
       else if 0 < x then fRight x - fRight 0 else 0)) := by
  sorry
