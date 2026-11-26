-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulCellsV2
-- name    : Kyprianou.Ch04.exercise41SuccessfulCellsV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:32:18.353127+00:00
-- url     : https://prove2.me/theorems/85e3ee3f-e8eb-44d7-b8d6-b47ec8df088f
-- title:
--   At most two successful near-zero cells under a positive slope bound
-- statement:
--   At most two successful near-zero cells under a positive slope bound
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulGapV1
import Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulCellCardV1
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41SuccessfulCellsV2
    (A : Finset ℕ) (τ v : ℕ → ℝ) (a h d : ℝ)
    (hh : 0 < h) (hd : 0 < d)
    (hcell : ∀ i ∈ A, a + (i : ℝ) * h ≤ τ i ∧
      τ i < a + ((i : ℝ) + 1) * h)
    (hnear : ∀ i ∈ A, |v i| < d * h / 8)
    (hslope : ∀ i ∈ A, ∀ j ∈ A, i < j →
      d / 2 * (τ j - τ i) ≤ v j - v i) :
    A.card ≤ 2  := by
  sorry
