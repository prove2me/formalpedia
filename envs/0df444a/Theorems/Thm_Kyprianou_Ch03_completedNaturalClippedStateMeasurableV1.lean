-- Prove2me | Theorems.Thm_Kyprianou_Ch03_completedNaturalClippedStateMeasurableV1
-- name    : Kyprianou.Ch03.completedNaturalClippedStateMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T22:01:02.610359+00:00
-- url     : https://prove2.me/theorems/42bbbc19-07de-4d45-ad41-f71d672bffb3
-- title:
--   Bounded stopped adapted right-continuous state is measurable in the completed filtration
-- statement:
--   Bounded stopped adapted right-continuous state is measurable in the completed filtration
-- source:
--   Kyprianou (2006), Exercise 3.2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.completedNaturalClippedStateMeasurableV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (Z : NNReal → Omega → ℝ) (hAdapt : Adapted F Z)
    (hRC : ∀ᵐ w ∂P, ∀ s : NNReal, ContinuousWithinAt (fun u => Z u w) (Ici s) s)
    (rho : Omega → NNReal)
    (hStop : IsStoppingTime F (fun w => (rho w : WithTop NNReal)))
    (s : NNReal) (hBound : ∀ w, rho w ≤ s) :
    Measurable[F s] (fun w => Z (rho w) w) := by
  sorry
