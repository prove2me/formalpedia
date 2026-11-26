-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ArrivalFromCutoffV22
-- name    : Kyprianou.Ch04.exercise41ArrivalFromCutoffV22
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T15:05:24.464274+00:00
-- url     : https://prove2.me/theorems/6651dbd7-953d-44a3-9863-c47ee525dfe5
-- title:
--   A negative point after the last preceding zero forces a negative left germ
-- statement:
--   A negative point after the last preceding zero forces a negative left germ
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41ArrivalFromCutoffV22
    (x : NNReal → ℝ)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → ∃ l, Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (hNeg : ∀ s l, 0 < s → Tendsto x (nhdsWithin s (Iio s)) (nhds l) → x s ≤ l)
    (a v s : NNReal) (hav : a < v) (hvs : v < s) (hv : x v < 0)
    (hgap : ∀ u ∈ Ico a s, x u ≠ 0) :
    ∃ e : NNReal, 0 < e ∧ ∀ u : NNReal, 0 < u → u < min e s → x (s-u) < 0 := by
  sorry
