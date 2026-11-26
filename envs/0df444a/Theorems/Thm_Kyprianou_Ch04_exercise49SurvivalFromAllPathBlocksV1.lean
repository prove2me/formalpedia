-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49SurvivalFromAllPathBlocksV1
-- name    : Kyprianou.Ch04.exercise49SurvivalFromAllPathBlocksV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:54:42.528818+00:00
-- url     : https://prove2.me/theorems/14e82066-b7b9-4ad9-badb-4ac11470ffb6
-- title:
--   Favourable blocks imply survival for an all-path measurable cadlag Levy version
-- statement:
--   Favourable blocks imply survival for an all-path measurable cadlag Levy version
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49SurvivalFromAllPathBlocksV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (hSafe : ∃ n : ℕ, 0 < P {ω | ∀ t : NNReal, -(n : ℝ) ≤ X t ω})
    (hBlock : ∃ s : NNReal, 0 < s ∧ ∃ a : ℝ, 0 < a ∧
      0 < P {ω | (∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ a ≤ X s ω}) :
    (P {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤}).toReal < 1 := by
  sorry
