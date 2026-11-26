-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49FutureSafeEventV1
-- name    : Kyprianou.Ch04.exercise49FutureSafeEventV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:56:59.907029+00:00
-- url     : https://prove2.me/theorems/7a4dfb6f-ad05-4546-b234-ce9558d9f5e7
-- title:
--   There is a measurable path event encoding a global lower bound
-- statement:
--   There is a measurable path event encoding a global lower bound
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49FutureSafeEventV1
    (b : ℝ) :
    ∃ B : Set (NNReal → ℝ), MeasurableSet B ∧
      ∀ Y : NNReal → ℝ, IsCadlag Y →
        (Y ∈ B ↔ ∀ t : NNReal, b ≤ Y t) := by
  sorry
