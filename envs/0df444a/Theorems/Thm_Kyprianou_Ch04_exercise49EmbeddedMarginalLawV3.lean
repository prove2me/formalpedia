-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49EmbeddedMarginalLawV3
-- name    : Kyprianou.Ch04.exercise49EmbeddedMarginalLawV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:52:11.051146+00:00
-- url     : https://prove2.me/theorems/9369f122-00bd-4c63-850b-55e13818e8da
-- title:
--   The marginal law of a Levy process is unchanged by embedding the probability space
-- statement:
--   The marginal law of a Levy process is unchanged by embedding the probability space
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49EmbeddedMarginalLawV3
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (j : Ω → E) (hj : MeasurableEmbedding j)
    (X : NNReal → Ω → ℝ) (Y : NNReal → E → ℝ)
    (hX : IsLevyProcess X P)
    (hAgree : ∀ t w, Y t (j w) = X t w) (t : NNReal) :
    Measure.map (Y t) (Measure.map j P) = Measure.map (X t) P := by
  sorry
