-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49FinitePathLowerBoundAEV1
-- name    : Kyprianou.Ch04.exercise49FinitePathLowerBoundAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:54:47.457596+00:00
-- url     : https://prove2.me/theorems/93e3e69f-4321-5954-a4e2-17cb810f8ca0
-- title:
--   Almost surely a cadlag process tending to infinity has a bounded all-time depth
-- statement:
--   Almost surely a cadlag process tending to infinity has a bounded all-time depth
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49FinitePathLowerBoundAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ w, IsCadlag (fun t => X t w))
    (hInf : ∀ᵐ w ∂P, Tendsto (fun t => X t w) atTop atTop) :
    ∀ᵐ w ∂P, BddAbove (Set.range (fun t => -X t w)) := by
  sorry
