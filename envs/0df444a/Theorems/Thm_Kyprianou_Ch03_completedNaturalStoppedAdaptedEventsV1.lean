-- Prove2me | Theorems.Thm_Kyprianou_Ch03_completedNaturalStoppedAdaptedEventsV1
-- name    : Kyprianou.Ch03.completedNaturalStoppedAdaptedEventsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:17:45.424798+00:00
-- url     : https://prove2.me/theorems/f3b6c8d5-8741-4278-8499-cb9b30871055
-- title:
--   Almost surely right-continuous adapted states are measurable on finite stopped-event slices
-- statement:
--   Clip the stopping time at s, use bounded countable upper stopping grids and adaptedness for measurable approximations. The right-continuous path limit agrees almost surely; the completed filtration contains the exceptional null set, so the stopped-event slice is exactly measurable. Countable union of finite slices gives the restricted almost-sure measurable state.
-- source:
--   Kyprianou (2006), Exercise 3.2: reflected Lévy processes are strong Markov.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.completedNaturalStoppedAdaptedEventsV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (Z : NNReal → Omega → ℝ) (hAdapt : Adapted F Z)
    (hRC : ∀ᵐ w ∂P, ∀ s : NNReal, ContinuousWithinAt (fun u => Z u w) (Ici s) s)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (r : Omega → NNReal) (hr : ∀ w, tau w ≠ ⊤ → tau w = (r w : WithTop NNReal))
    (A : Set Omega)
    (hA : ∀ s : NNReal, MeasurableSet[F s] (A ∩ {w | tau w ≤ (s : WithTop NNReal)})) :
    AEMeasurable (fun w => Z (r w) w) (P.restrict (A ∩ {w | tau w ≠ ⊤})) ∧
    ∀ (B : Set ℝ), MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s] ((A ∩ {w | Z (r w) w ∈ B}) ∩
        {w | tau w ≤ (s : WithTop NNReal)}) := by
  sorry
