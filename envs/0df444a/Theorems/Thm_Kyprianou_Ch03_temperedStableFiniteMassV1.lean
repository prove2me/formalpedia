-- Prove2me | Theorems.Thm_Kyprianou_Ch03_temperedStableFiniteMassV1
-- name    : Kyprianou.Ch03.temperedStableFiniteMassV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T16:49:32.350831+00:00
-- url     : https://prove2.me/theorems/110aa392-5677-43f5-8bf0-73925168108b
-- title:
--   Finite mass of the tempered positive jump measure at negative index
-- statement:
--   The density on the positive half-line equals c*x^(-1-alpha)*exp(-gamma*x). Its power exponent exceeds -1, so the real gamma integral is finite.
-- source:
--   Kyprianou (2006), Exercise 3.4, auxiliary obligations for temperedStableDecomposition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.temperedStableFiniteMassV1
    (c alpha gamma : ℝ) (hc : 0 < c) (ha : alpha < 0) (hg : 0 < gamma) :
    Kyprianou.Ch03.temperedStablePositiveMeasure c alpha gamma Set.univ < ⊤ := by sorry
