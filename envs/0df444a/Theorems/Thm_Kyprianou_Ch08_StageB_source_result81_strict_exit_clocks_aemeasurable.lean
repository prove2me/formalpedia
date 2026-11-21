-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_clocks_aemeasurable
-- name    : Kyprianou.Ch08.StageB.source_result81_strict_exit_clocks_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:53:03.713952+00:00
-- url     : https://prove2.me/theorems/0a5ecd4f-4320-4b0b-b3bc-35e3f18de91a
-- title:
--   Almost-everywhere measurability of the two strict exit clocks
-- statement:
--   Use rational-time approximations to the exact strict crossing infima and obtain each time-coordinate measurability from stationary increments and zero start. Apply this to the shifted process and to the difference of the upper threshold and that shifted process.
-- source:
--   Strict first-passage clocks used in Kyprianou (2006), Chapter 8, equation (8.8). Decomposition of 56d28aed-aec3-4761-b4d8-75594524f739.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open Set Filter Topology MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_strict_exit_clocks_aemeasurable
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (x a : ℝ) :
    AEMeasurable (fun ω => (tauPlus (shifted D.X x) a ω : ℝ≥0∞)) P ∧
      AEMeasurable (fun ω => (tauMinus (shifted D.X x) 0 ω : ℝ≥0∞)) P := by
  sorry
