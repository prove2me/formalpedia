-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_positive_time_shift
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_factor_positive_time_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T03:45:47.813311+00:00
-- url     : https://prove2.me/theorems/dd324f45-dd0a-4d05-bf2d-3c48daaec7ac
-- title:
--   Positive-time random shift identity
-- statement:
--   For any measurable nonnegative random time and any jointly measurable nonnegative time-space reward, integrating the reward after the random time with respect to positive time Lebesgue measure equals integrating the reward over all times with the indicator that the time is at or after the random time.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m87_qpos_factor_positive_time_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (U : Ω → ℝ≥0) (hU : Measurable U)
    (F : ℝ≥0 → Ω → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ ω, ∫⁻ s : ℝ≥0, F (U ω + s) ω ∂positiveTimeLebesgue ∂P) =
      ∫⁻ ω, ∫⁻ t : ℝ≥0, if U ω ≤ t then F t ω else 0 ∂positiveTimeLebesgue ∂P := by
  sorry
