-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49AllPathCadlagVersionV1
-- name    : Kyprianou.Ch04.exercise49AllPathCadlagVersionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:54:40.285516+00:00
-- url     : https://prove2.me/theorems/aa472b1b-716b-56e3-a41f-13f1feac6488
-- title:
--   A measurable all-path cadlag Levy version with indistinguishable paths
-- statement:
--   A measurable all-path cadlag Levy version with indistinguishable paths
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49AllPathCadlagVersionV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P) :
    ∃ Y : NNReal → Ω → ℝ, IsLevyProcess Y P ∧
      (∀ t, Measurable (Y t)) ∧ (∀ ω, IsCadlag (fun t => Y t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t, Y t ω = X t ω) := by
  sorry
