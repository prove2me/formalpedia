-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41LocalNonzeroV12
-- name    : Kyprianou.Ch04.exercise41LocalNonzeroV12
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:51:48.968282+00:00
-- url     : https://prove2.me/theorems/bca0a401-ee8c-48f0-8ac1-929f710c4bb8
-- title:
--   A nonzero cadlag value and nonzero left limit give a full neighbourhood bounded away from zero
-- statement:
--   A nonzero cadlag value and nonzero left limit give a full neighbourhood bounded away from zero
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), zero-visit boundary behaviour.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41LocalNonzeroV12
    (x : NNReal → ℝ) (s : NNReal) (l : ℝ)
    (hx : x s ≠ 0) (hl : l ≠ 0)
    (hR : ContinuousWithinAt x (Ici s) s)
    (hL : Tendsto x (nhdsWithin s (Iio s)) (nhds l)) :
    ∃ e : ℝ, 0 < e ∧ {v : NNReal | e ≤ |x v|} ∈ nhds s := by
  sorry
