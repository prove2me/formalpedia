-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49EmbeddedIdentDistribV3
-- name    : Kyprianou.Ch04.exercise49EmbeddedIdentDistribV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:49:02.054697+00:00
-- url     : https://prove2.me/theorems/3423c1b9-8d6c-4511-a197-69a17e55d16c
-- title:
--   Identical distributions transfer across a measurable embedding
-- statement:
--   Identical distributions transfer across a measurable embedding
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49EmbeddedIdentDistribV3
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (j : Ω → E) (hj : MeasurableEmbedding j)
    (f g : E → ℝ) (h : IdentDistrib (f ∘ j) (g ∘ j) P P) :
    IdentDistrib f g (Measure.map j P) (Measure.map j P) := by
  sorry
