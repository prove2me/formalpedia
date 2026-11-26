-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49EmbeddedIndependentV3
-- name    : Kyprianou.Ch04.exercise49EmbeddedIndependentV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:48:58.736566+00:00
-- url     : https://prove2.me/theorems/858d59ea-5271-4f1e-a7b6-cb0d32ee53fe
-- title:
--   Independent random variables remain independent under a measurable embedding of the probability space
-- statement:
--   Independent random variables remain independent under a measurable embedding of the probability space
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49EmbeddedIndependentV3
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (j : Ω → E) (hj : MeasurableEmbedding j)
    (f : ι → E → ℝ)
    (h : iIndepFun (fun i w => f i (j w)) P) :
    iIndepFun f (Measure.map j P) := by
  sorry
