-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PrefixSafeFinishV1
-- name    : Kyprianou.Ch04.exercise49PrefixSafeFinishV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:56:53.354578+00:00
-- url     : https://prove2.me/theorems/1153b5c7-a658-4f32-a884-0f86d7660846
-- title:
--   A favourable prefix attaining a safe reserve gives strictly subunit ruin probability
-- statement:
--   A favourable prefix attaining a safe reserve gives strictly subunit ruin probability
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PrefixSafeFinishV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (s : NNReal) (b : ℝ)
    (hA : 0 < P {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω})
    (hB : 0 < P {ω | ∀ u : NNReal, -b ≤ X u ω}) :
    (P {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤}).toReal < 1 := by
  sorry
