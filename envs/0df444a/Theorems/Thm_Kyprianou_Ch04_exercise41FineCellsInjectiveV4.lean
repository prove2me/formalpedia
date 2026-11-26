-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FineCellsInjectiveV4
-- name    : Kyprianou.Ch04.exercise41FineCellsInjectiveV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:24:23.845952+00:00
-- url     : https://prove2.me/theorems/007cfdfb-bf26-56d5-8ff5-a720bbd5675a
-- title:
--   Shrinking cell widths eventually separate each fixed finite collection of distinct times
-- statement:
--   Shrinking cell widths eventually separate each fixed finite collection of distinct times
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FineCellsInjectiveV4
    (S : Finset NNReal) (a : ℝ) (h : ℕ → ℝ)
    (ht : Tendsto h atTop (𝓝 0))
    (j : ℕ → NNReal → ℕ)
    (hc : ∀ n s, s ∈ S → a + (j n s : ℝ) * h n ≤ (s : ℝ) ∧
      (s : ℝ) < a + ((j n s : ℝ) + 1) * h n) :
    ∀ᶠ n in atTop, Set.InjOn (j n) (S : Set NNReal)  := by
  sorry
