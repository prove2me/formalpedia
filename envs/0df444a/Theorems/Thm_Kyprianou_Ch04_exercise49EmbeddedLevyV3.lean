-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49EmbeddedLevyV3
-- name    : Kyprianou.Ch04.exercise49EmbeddedLevyV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:52:07.208016+00:00
-- url     : https://prove2.me/theorems/7cbfb68e-c274-4244-ba39-606cb9538afd
-- title:
--   A process extended along a measurable embedding preserves the Levy axioms
-- statement:
--   A process extended along a measurable embedding preserves the Levy axioms
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49EmbeddedLevyV3
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (j : Ω → E) (hj : MeasurableEmbedding j)
    (X : NNReal → Ω → ℝ) (Y : NNReal → E → ℝ)
    (hX : IsLevyProcess X P) (hY0 : Y 0 = fun _ => 0)
    (hAgree : ∀ t w, Y t (j w) = X t w) :
    IsLevyProcess Y (Measure.map j P) := by
  sorry
