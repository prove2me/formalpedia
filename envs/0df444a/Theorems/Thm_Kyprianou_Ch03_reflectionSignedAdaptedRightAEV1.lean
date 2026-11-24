-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionSignedAdaptedRightAEV1
-- name    : Kyprianou.Ch03.reflectionSignedAdaptedRightAEV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T21:47:40.514817+00:00
-- url     : https://prove2.me/theorems/9ffcff5e-6479-41ce-863b-35c820df5566
-- title:
--   Signed reflection adapted and almost surely right continuous
-- statement:
--   Use the countable dense-prefix maximum for adaptation, completion for exceptional paths, and the running maximum right continuity theorem.
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

theorem Kyprianou.Ch03.reflectionSignedAdaptedRightAEV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (c y : ℝ) :
    (∀ s : NNReal, Measurable[F s] (reflectedSup (fun u v => c * X u v) y s)) ∧
    (∀ᵐ w ∂P, ∀ s : NNReal,
      ContinuousWithinAt (fun u => reflectedSup (fun v z => c * X v z) y u w) (Set.Ici s) s) := by sorry
