-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SmoothJoinDerivLimitV11
-- name    : Kyprianou.Ch04.exercise41SmoothJoinDerivLimitV11
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:45:49.687832+00:00
-- url     : https://prove2.me/theorems/0e7bce7f-ca88-46dd-9d66-c034ca67c3c7
-- title:
--   Pointwise derivative convergence includes zero, where both ramp derivatives tend to zero
-- statement:
--   Pointwise derivative convergence includes zero, where both ramp derivatives tend to zero
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41SmoothJoinDerivLimitV11
    (fLeft fRight : ℝ → ℝ)
    (hL : ContDiff ℝ 1 fLeft) (hR : ContDiff ℝ 1 fRight)
    (p : ℕ → ℝ → ℝ)
    (hP : ∀ x, Tendsto (fun n => p n x) atTop (𝓝 (max 0 x)))
    (hD : ∀ x, Tendsto (fun n => deriv (p n) x) atTop
      (𝓝 (if 0 < x then 1 else 0)))
    (x : ℝ) :
    Tendsto (fun n => deriv fLeft (-p n (-x)) * deriv (p n) (-x) +
      deriv fRight (p n x) * deriv (p n) x) atTop (𝓝
      (if x < 0 then deriv fLeft x else if 0 < x then deriv fRight x else 0)) := by
  sorry
