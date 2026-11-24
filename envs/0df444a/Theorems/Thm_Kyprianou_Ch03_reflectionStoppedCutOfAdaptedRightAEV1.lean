-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionStoppedCutOfAdaptedRightAEV1
-- name    : Kyprianou.Ch03.reflectionStoppedCutOfAdaptedRightAEV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T21:47:45.195834+00:00
-- url     : https://prove2.me/theorems/c422f1fe-1a7d-47d5-85b4-da00ad51931e
-- title:
--   Stopped cuts of an adapted almost surely right-continuous process
-- statement:
--   Approximate the capped stopping clock from above by countable-valued stopping clocks bounded by the cap. Use right continuity and the completed filtration to transfer the limit.
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

theorem Kyprianou.Ch03.reflectionStoppedCutOfAdaptedRightAEV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (R : NNReal → Omega → ℝ)
    (hAdapt : ∀ s : NNReal, Measurable[F s] (R s))
    (hRight : ∀ᵐ w ∂P, ∀ s : NNReal,
      ContinuousWithinAt (fun u => R u w) (Set.Ici s) s)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal)) :
    ∀ B : Set ℝ, MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s] ({w | R (finiteTime w) w ∈ B}
        ∩ {w | tau w ≤ (s : WithTop NNReal)}) := by sorry
