-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionStoppedStateRestrictedMeasV1
-- name    : Kyprianou.Ch03.reflectionStoppedStateRestrictedMeasV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T21:48:00.164453+00:00
-- url     : https://prove2.me/theorems/b63b34fa-9b3f-4c7b-b8ce-ebe204fc88e8
-- title:
--   Measurability on a finite stopped event
-- statement:
--   Finite stopping-time cuts exhaust the event, so the stopped state has measurable restriction.
-- source:
--   Kyprianou (2006), Exercise 3.2, stopped-state kernel proof.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectionStoppedStateRestrictedMeasV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (A : Set Omega)
    (hA : ∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    (S : Omega → ℝ)
    (hS : ∀ B : Set ℝ, MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s] ({w | S w ∈ B} ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    : AEMeasurable S (P.restrict (A ∩ {w | tau w ≠ ⊤})) := by sorry
