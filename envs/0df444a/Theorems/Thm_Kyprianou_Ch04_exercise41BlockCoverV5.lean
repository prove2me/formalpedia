-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BlockCoverV5
-- name    : Kyprianou.Ch04.exercise41BlockCoverV5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T08:44:30.505904+00:00
-- url     : https://prove2.me/theorems/d3d0709c-1ff0-4c0a-862c-aab9145ec5d9
-- title:
--   Finite zero visits in all fixed-width blocks imply local finiteness on the whole time axis
-- statement:
--   Finite zero visits in all fixed-width blocks imply local finiteness on the whole time axis
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41BlockCoverV5
    (x : NNReal → ℝ) (δ : NNReal) (hδ : 0 < δ)
    (h : ∀ k : ℕ, Set.Finite
      {s : NNReal | (k : NNReal) * δ ≤ s ∧
        s < (k : NNReal) * δ + δ ∧ x s = 0}) :
    ∀ t : NNReal, Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ x s = 0}  := by
  sorry
