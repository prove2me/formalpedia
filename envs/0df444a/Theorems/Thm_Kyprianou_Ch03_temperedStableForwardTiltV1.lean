-- Prove2me | Theorems.Thm_Kyprianou_Ch03_temperedStableForwardTiltV1
-- name    : Kyprianou.Ch03.temperedStableForwardTiltV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:49:39.741865+00:00
-- url     : https://prove2.me/theorems/c8cbcd34-f338-4930-ae06-93b87e8f448f
-- title:
--   Tempering a positive stable jump measure by exponential density
-- statement:
--   Multiply the density of the untempered positive measure by exp(-gamma*x), using withDensity_mul and the defining piecewise density.
-- source:
--   Kyprianou (2006), Exercise 3.4, auxiliary obligations for temperedStableDecomposition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.temperedStableForwardTiltV1
    (c alpha gamma : ℝ) (hc : 0 < c) (hg : 0 < gamma) :
    Kyprianou.Ch03.temperedStablePositiveMeasure c alpha gamma =
      (Kyprianou.Ch03.temperedStablePositiveMeasure c alpha 0).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-gamma*x))) := by sorry
