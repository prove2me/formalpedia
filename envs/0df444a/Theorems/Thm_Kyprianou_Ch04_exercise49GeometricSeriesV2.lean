-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49GeometricSeriesV2
-- name    : Kyprianou.Ch04.exercise49GeometricSeriesV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:31:56.608829+00:00
-- url     : https://prove2.me/theorems/aefbb8fa-8bed-5630-85d4-c9fddf12b2c6
-- title:
--   Geometric renewal remainder gives infinite expansion
-- statement:
--   Geometric renewal remainder gives infinite expansion
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49GeometricSeriesV2
    (rho : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho < 1)
    (u r : ℕ → ℝ)
    (hu : ∀ k, 0 ≤ u k)
    (hr : ∀ n, 0 ≤ r n ∧ r n ≤ rho ^ n)
    (hrec : ∀ n, r n = (1 - rho) * (rho ^ n * u n) + r (n + 1)) :
    r 0 = (1 - rho) * ∑' k, rho ^ k * u k  := by
  sorry
