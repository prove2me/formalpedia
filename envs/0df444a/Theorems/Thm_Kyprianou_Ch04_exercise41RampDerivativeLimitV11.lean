-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41RampDerivativeLimitV11
-- name    : Kyprianou.Ch04.exercise41RampDerivativeLimitV11
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:45:11.728201+00:00
-- url     : https://prove2.me/theorems/7fc7ecac-baab-4ba0-aaf7-b086a42e0905
-- title:
--   Pointwise convergence of clipped ramp derivatives to the strict positive indicator
-- statement:
--   Pointwise convergence of clipped ramp derivatives to the strict positive indicator
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41RampDerivativeLimitV11
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => min (1 : ℝ) (max 0 (x / ε n))) atTop
      (𝓝 (if 0 < x then 1 else 0)) := by
  sorry
