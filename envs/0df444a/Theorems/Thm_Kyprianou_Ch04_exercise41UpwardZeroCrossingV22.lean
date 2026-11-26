-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41UpwardZeroCrossingV22
-- name    : Kyprianou.Ch04.exercise41UpwardZeroCrossingV22
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:05:22.866534+00:00
-- url     : https://prove2.me/theorems/83722bf3-914c-5377-b207-8bc3fe7ed4ac
-- title:
--   A cadlag path without positive jumps crosses zero between a negative and a positive value
-- statement:
--   A cadlag path without positive jumps crosses zero between a negative and a positive value
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41UpwardZeroCrossingV22
    (x : NNReal → ℝ)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → ∃ l, Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (hNeg : ∀ s l, 0 < s → Tendsto x (nhdsWithin s (Iio s)) (nhds l) → x s ≤ l)
    (a b : NNReal) (hab : a ≤ b) (ha : x a < 0) (hb : 0 ≤ x b) :
    ∃ c ∈ Icc a b, x c = 0 := by
  sorry
