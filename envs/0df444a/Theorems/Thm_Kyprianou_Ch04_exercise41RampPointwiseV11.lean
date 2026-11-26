-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41RampPointwiseV11
-- name    : Kyprianou.Ch04.exercise41RampPointwiseV11
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:45:12.946662+00:00
-- url     : https://prove2.me/theorems/77c0d598-3c2e-4077-8a3e-e875724e9e46
-- title:
--   Pointwise convergence of ramp primitives to the positive part
-- statement:
--   Pointwise convergence of ramp primitives to the positive part
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41RampPointwiseV11
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    let r := fun (n : ℕ) (u : ℝ) => min 1 (max 0 (u / ε n))
    let p := fun (n : ℕ) (x : ℝ) => ∫ u in (0 : ℝ)..x, r n u
    Tendsto (fun n => p n x) atTop (𝓝 (max 0 x)) := by
  sorry
