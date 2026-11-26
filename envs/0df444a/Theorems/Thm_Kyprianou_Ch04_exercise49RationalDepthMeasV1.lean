-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RationalDepthMeasV1
-- name    : Kyprianou.Ch04.exercise49RationalDepthMeasV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:45:32.98132+00:00
-- url     : https://prove2.me/theorems/940a30f9-4f9e-5709-8279-15eb8b17c880
-- title:
--   Measurable real all-time depth from countably many rational coordinates
-- statement:
--   Measurable real all-time depth from countably many rational coordinates
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49RationalDepthMeasV1
    : Measurable (fun Y : NNReal → ℝ => (⨆ q : ℚ, ENNReal.ofReal (-Y (Real.toNNReal q))).toReal) := by
  sorry
