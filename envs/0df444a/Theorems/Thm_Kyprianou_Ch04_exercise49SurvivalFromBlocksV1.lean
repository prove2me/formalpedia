-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49SurvivalFromBlocksV1
-- name    : Kyprianou.Ch04.exercise49SurvivalFromBlocksV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T12:48:30.012987+00:00
-- url     : https://prove2.me/theorems/c6b1200d-d0c1-44d6-81c1-64e68ac1a00e
-- title:
--   Independent concatenation of favourable blocks and a safe reserve gives a strictly subunit ruin probability
-- statement:
--   Independent concatenation of favourable blocks and a safe reserve gives a strictly subunit ruin probability
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49SurvivalFromBlocksV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hSafe : ∃ n : ℕ, 0 < P {ω | ∀ t : NNReal, -(n : ℝ) ≤ X t ω})
    (hBlock : ∃ s : NNReal, 0 < s ∧ ∃ a : ℝ, 0 < a ∧
      0 < P {ω | (∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ a ≤ X s ω}) :
    (P {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤}).toReal < 1 := by
  sorry
