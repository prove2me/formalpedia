-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PositiveSurvivalRuinBoundV1
-- name    : Kyprianou.Ch04.exercise49PositiveSurvivalRuinBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:01:59.84037+00:00
-- url     : https://prove2.me/theorems/ad6d581f-2f12-478f-9fd9-9f07bde83872
-- title:
--   Positive survival mass implies strict upper bound on eventual ruin probability
-- statement:
--   Positive survival mass implies strict upper bound on eventual ruin probability
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PositiveSurvivalRuinBoundV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (hS : 0 < P {ω | ∀ u : NNReal, 0 ≤ X u ω}) :
    (P {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤}).toReal < 1 := by
  sorry
