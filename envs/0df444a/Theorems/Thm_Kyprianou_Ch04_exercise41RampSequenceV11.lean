-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41RampSequenceV11
-- name    : Kyprianou.Ch04.exercise41RampSequenceV11
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:47:05.942878+00:00
-- url     : https://prove2.me/theorems/cb1eff0b-fb6d-5196-9b19-0429fcef393d
-- title:
--   Construct a smooth positive-part approximating sequence with derivative in [0,1] and exact pointwise limits
-- statement:
--   Construct a smooth positive-part approximating sequence with derivative in [0,1] and exact pointwise limits
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41RampSequenceV11 :
    ∃ p : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ 1 (p n)) ∧
      (∀ n x, 0 ≤ p n x ∧ p n x ≤ max 0 x) ∧
      (∀ x, Tendsto (fun n => p n x) atTop (𝓝 (max 0 x))) ∧
      (∀ n x, 0 ≤ deriv (p n) x ∧ deriv (p n) x ≤ 1) ∧
      (∀ x, Tendsto (fun n => deriv (p n) x) atTop (𝓝 (if 0 < x then 1 else 0))) := by
  sorry
