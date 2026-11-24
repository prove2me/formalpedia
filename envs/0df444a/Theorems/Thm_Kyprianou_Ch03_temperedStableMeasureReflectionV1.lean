-- Prove2me | Theorems.Thm_Kyprianou_Ch03_temperedStableMeasureReflectionV1
-- name    : Kyprianou.Ch03.temperedStableMeasureReflectionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:49:29.956787+00:00
-- url     : https://prove2.me/theorems/b19952ee-dae2-457d-a956-63a0769ed6ab
-- title:
--   Lévy measure property under reflection
-- statement:
--   Use map_apply on the singleton zero and lintegral_map with the even integrand min(1,x²).
-- source:
--   Kyprianou (2006), Exercise 3.4, auxiliary obligations for temperedStableDecomposition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.temperedStableMeasureReflectionV1
    (mu : Measure ℝ) (hm : IsLevyMeasure (mu.map (fun x : ℝ => -x))) :
    IsLevyMeasure mu := by sorry
