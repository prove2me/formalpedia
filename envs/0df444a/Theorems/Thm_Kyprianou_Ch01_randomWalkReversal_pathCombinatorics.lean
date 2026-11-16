-- Prove2me | Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_pathCombinatorics
-- name    : Kyprianou.Ch01.randomWalkReversal_pathCombinatorics
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T17:18:03.017977+00:00
-- url     : https://prove2.me/theorems/466712c2-3333-4f43-b468-c2b5656475b7
-- title:
--   Reversal exchanges strict terminal maxima with strictly positive reversed prefixes
-- statement:
--   For any deterministic finite sequence of real increments, every earlier prefix sum is strictly smaller than the terminal sum exactly when every non-empty prefix sum of the reversed increment sequence is strictly positive. The terminal sums before and after reversal agree, so membership in any set B is preserved.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.8(i), deterministic ladder reversal identity

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.randomWalkReversal_pathCombinatorics
    (a : ℕ → ℝ) (n : ℕ) (B : Set ℝ) :
    ((∑ i ∈ Finset.range n, a i) ∈ B ∧
      ∀ j : ℕ, j < n →
        (∑ i ∈ Finset.range j, a i) < (∑ i ∈ Finset.range n, a i)) ↔
    ((∑ i ∈ Finset.range n, a (n - 1 - i)) ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n →
        0 < (∑ i ∈ Finset.range j, a (n - 1 - i))) := by sorry
