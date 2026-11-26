-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41MeasurableGridInfimumV26
-- name    : Kyprianou.Ch04.exercise41MeasurableGridInfimumV26
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:43:23.48503+00:00
-- url     : https://prove2.me/theorems/52fdfb97-9b38-43bf-bb05-0cd4b69b6c46
-- title:
--   exercise41MeasurableGridInfimumV26
-- statement:
--   Measurability of the dense grid infimum.
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41MeasurableGridInfimumV26
    (q : ℕ → NNReal) (h : NNReal) :
    Measurable (fun f : NNReal → ℝ => ⨅ k : ℕ, f (min (q k) h)) := by
  sorry
