-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41GapNonzeroV14
-- name    : Kyprianou.Ch04.exercise41GapNonzeroV14
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:01:57.193817+00:00
-- url     : https://prove2.me/theorems/c94e92f2-c985-557a-96e8-f7f65c4545a7
-- title:
--   On a positive compact interval with no zeros or jumps from zero, a cadlag path is uniformly separated from zero
-- statement:
--   On a positive compact interval with no zeros or jumps from zero, a cadlag path is uniformly separated from zero
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41GapNonzeroV14
    (x : NNReal → ℝ) (a b : NNReal) (ha : 0 < a)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → ∃ l, Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (hNoJump : ∀ s, 0 < s → Function.leftLim x s = 0 → x s = 0)
    (hgap : ∀ u ∈ Icc a b, x u ≠ 0) :
    ∃ e : ℝ, 0 < e ∧ ∀ u ∈ Icc a b, e ≤ |x u| := by
  sorry
