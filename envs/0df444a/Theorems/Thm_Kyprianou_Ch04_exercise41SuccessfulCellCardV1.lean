-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulCellCardV1
-- name    : Kyprianou.Ch04.exercise41SuccessfulCellCardV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:42:52.417407+00:00
-- url     : https://prove2.me/theorems/39b5689c-6ea8-4670-b538-5358da944503
-- title:
--   At most two successful cells in a restart grid
-- statement:
--   If chosen times in occupied cells have all ordered pair gaps less than the cell width, all occupied cell indices lie among the smallest index and its successor.
-- source:
--   Kyprianou (2006), Exercise 4.1(i)–(ii), printed pp.105–106.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise41SuccessfulCellCardV1
    (A : Finset ℕ) (τ : ℕ → ℝ) (a h : ℝ) (hh : 0 < h)
    (hcell : ∀ i ∈ A, a + (i : ℝ) * h ≤ τ i ∧
      τ i < a + ((i : ℝ) + 1) * h)
    (hgap : ∀ i ∈ A, ∀ j ∈ A, i < j → τ j - τ i < h) :
    A.card ≤ 2 := by
  sorry
