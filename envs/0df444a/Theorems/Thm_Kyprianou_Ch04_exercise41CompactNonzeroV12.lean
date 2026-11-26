-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41CompactNonzeroV12
-- name    : Kyprianou.Ch04.exercise41CompactNonzeroV12
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:51:47.841876+00:00
-- url     : https://prove2.me/theorems/590143f4-a079-5a30-a513-aa0de9e10f92
-- title:
--   Compactness turns local nonzero lower bounds into a common positive lower bound
-- statement:
--   Compactness turns local nonzero lower bounds into a common positive lower bound
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), zero-visit boundary behaviour.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41CompactNonzeroV12
    (x : NNReal → ℝ) (a b : NNReal)
    (hLoc : ∀ s ∈ Icc a b, ∃ e : ℝ, 0 < e ∧
      {v : NNReal | e ≤ |x v|} ∈ nhds s) :
    ∃ e : ℝ, 0 < e ∧ ∀ s ∈ Icc a b, e ≤ |x s| := by
  sorry
