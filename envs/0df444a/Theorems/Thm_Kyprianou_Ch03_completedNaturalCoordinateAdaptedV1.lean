-- Prove2me | Theorems.Thm_Kyprianou_Ch03_completedNaturalCoordinateAdaptedV1
-- name    : Kyprianou.Ch03.completedNaturalCoordinateAdaptedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T22:00:58.531046+00:00
-- url     : https://prove2.me/theorems/319ceda2-5523-45f8-b839-652de7fcf2e4
-- title:
--   Coordinates are adapted to the completed natural filtration
-- statement:
--   Coordinates are adapted to the completed natural filtration
-- source:
--   Kyprianou (2006), Exercise 3.2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.completedNaturalCoordinateAdaptedV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F) :
    Adapted F X := by
  sorry
