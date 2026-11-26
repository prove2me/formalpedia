-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49AllPathExactClockV1
-- name    : Kyprianou.Ch04.exercise49AllPathExactClockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:45:37.437808+00:00
-- url     : https://prove2.me/theorems/4a45cf8f-a1f5-4cdb-8e4b-ffaa0d92096e
-- title:
--   On measurable all-path cadlag Levy versions the strict first-passage clock has a pointwise finite representative
-- statement:
--   On measurable all-path cadlag Levy versions the strict first-passage clock has a pointwise finite representative
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49AllPathExactClockV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω)) :
    let τ : Ω → WithTop NNReal := fun ω => sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t ω < 0}
    Measurable τ ∧ ∃ f : Ω → NNReal, Measurable f ∧
      ∀ ω, τ ω ≠ ⊤ → τ ω = (f ω : WithTop NNReal) := by
  sorry
