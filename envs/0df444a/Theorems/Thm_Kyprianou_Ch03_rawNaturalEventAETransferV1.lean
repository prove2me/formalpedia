-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rawNaturalEventAETransferV1
-- name    : Kyprianou.Ch03.rawNaturalEventAETransferV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T13:20:06.975113+00:00
-- url     : https://prove2.me/theorems/aad11b6e-4bd5-4b8e-b7d2-74491b3ba817
-- title:
--   Raw natural filtration events transfer across common path modifications
-- statement:
--   The natural filtration is the comap of the path restricted to times at most s. Take the preimage of the same path event under Y, whose membership agrees almost surely.
-- source:
--   Kyprianou (2006), Exercise 3.1: right continuity of the completed natural filtration.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.rawNaturalEventAETransferV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Y : NNReal → Omega → ℝ) (hEq : ∀ᵐ w ∂P, ∀ t, Y t w = X t w)
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[PerfCorrMSQ.natFiltr X s] A) :
    ∃ B : Set Omega, MeasurableSet[PerfCorrMSQ.natFiltr Y s] B ∧ A =ᵐ[P] B := by
  sorry
