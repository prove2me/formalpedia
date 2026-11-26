-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41RealGermFromNNRealV16
-- name    : Kyprianou.Ch04.exercise41RealGermFromNNRealV16
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:11:26.223311+00:00
-- url     : https://prove2.me/theorems/354a3505-d890-4583-88ed-eb712f591c40
-- title:
--   Convert a positive increment germ at nonnegative time to a real-time increasing right germ
-- statement:
--   Convert a positive increment germ at nonnegative time to a real-time increasing right germ
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), exclusion of continuous touches from above.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41RealGermFromNNRealV16
    (x : NNReal → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (e : NNReal) (he : 0 < e)
    (h : ∀ u : NNReal, 0 < u → u < e → x (s.toNNReal + u) - x s.toNNReal > 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Ioo s (s+δ), x s.toNNReal < x v.toNNReal := by
  sorry
