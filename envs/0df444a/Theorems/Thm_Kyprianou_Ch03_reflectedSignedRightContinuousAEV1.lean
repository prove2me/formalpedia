-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectedSignedRightContinuousAEV1
-- name    : Kyprianou.Ch03.reflectedSignedRightContinuousAEV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:17:29.947303+00:00
-- url     : https://prove2.me/theorems/68e016b7-1998-4a01-acc4-4e98fd584293
-- title:
--   Signed reflected path is almost surely right-continuous
-- statement:
--   The signed path is càdlàg and bounded on each compact interval. Its running supremum is monotone, dominates the path, and is right-continuous by the proved running-supremum theorem. Max with the initial level and subtract the signed coordinate.
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

theorem Kyprianou.Ch03.reflectedSignedRightContinuousAEV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (c y : ℝ) :
    ∀ᵐ w ∂P, ∀ s : NNReal,
      ContinuousWithinAt (fun u => reflectedSup (fun v z => c * X v z) y u w) (Ici s) s := by
  sorry
