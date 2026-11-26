-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PrefixEventRawMeasurableV1
-- name    : Kyprianou.Ch04.exercise49PrefixEventRawMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:57:00.150569+00:00
-- url     : https://prove2.me/theorems/775cac46-bb80-4a30-afa7-6e0cf15451e6
-- title:
--   The nonnegative prefix and endpoint gain event is raw-past measurable
-- statement:
--   The nonnegative prefix and endpoint gain event is raw-past measurable
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PrefixEventRawMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (X : NNReal → Ω → ℝ)
    (hc : ∀ ω, IsCadlag (fun t => X t ω)) (s : NNReal) (b : ℝ) :
    MeasurableSet[PerfCorrMSQ.natFiltr X s]
      {ω | (∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ b ≤ X s ω} := by
  sorry
