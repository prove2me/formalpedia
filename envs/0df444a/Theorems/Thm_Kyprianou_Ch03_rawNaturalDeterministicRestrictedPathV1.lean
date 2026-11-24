-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rawNaturalDeterministicRestrictedPathV1
-- name    : Kyprianou.Ch03.rawNaturalDeterministicRestrictedPathV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:20:01.361801+00:00
-- url     : https://prove2.me/theorems/97958299-e084-4d85-bc9e-344a76c4eb72
-- title:
--   Deterministic future path law restricted to a raw natural filtration event
-- statement:
--   Use the natural filtration, independent increments, the proved deterministic restricted finite-dimensional laws, and uniqueness of path laws from finite pushforwards.
-- source:
--   Kyprianou (2006), Exercise 3.1: right continuity of the completed natural filtration.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.rawNaturalDeterministicRestrictedPathV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (hMeas : ∀ t, Measurable (X t))
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[PerfCorrMSQ.natFiltr X s] A) :
    Measure.map (fun (w : Omega) (u : NNReal) => X (s + u) w - X s w) (P.restrict A) =
      P A • Measure.map (fun (w : Omega) (u : NNReal) => X u w) P := by
  sorry
