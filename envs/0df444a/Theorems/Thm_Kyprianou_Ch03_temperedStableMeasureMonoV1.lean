-- Prove2me | Theorems.Thm_Kyprianou_Ch03_temperedStableMeasureMonoV1
-- name    : Kyprianou.Ch03.temperedStableMeasureMonoV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:49:35.266801+00:00
-- url     : https://prove2.me/theorems/032bd031-190a-49a7-a513-8fe94182ce7c
-- title:
--   Lévy measure property inherited by a dominated measure
-- statement:
--   Use measure monotonicity at zero and monotonicity of the nonnegative Lévy integrability integral.
-- source:
--   Kyprianou (2006), Exercise 3.4, auxiliary obligations for temperedStableDecomposition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.temperedStableMeasureMonoV1
    (mu nu : Measure ℝ) (hle : mu ≤ nu) (hn : IsLevyMeasure nu) :
    IsLevyMeasure mu := by sorry
