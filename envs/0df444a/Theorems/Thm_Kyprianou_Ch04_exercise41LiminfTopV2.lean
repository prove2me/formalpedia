-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41LiminfTopV2
-- name    : Kyprianou.Ch04.exercise41LiminfTopV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:31:59.784795+00:00
-- url     : https://prove2.me/theorems/865b28be-0d86-4e4a-be55-886528b1bedd
-- title:
--   Eventually arbitrarily large counts have infinite lower limit
-- statement:
--   Eventually arbitrarily large counts have infinite lower limit
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41LiminfTopV2 (N : ℕ → ℝ≥0∞)
    (hN : ∀ k : ℕ, ∃ m : ℕ, ∀ n ≥ m, (k : ℝ≥0∞) ≤ N n) :
    Filter.liminf N atTop = ⊤  := by
  sorry
