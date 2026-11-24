-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_enreal_stopped_reward_factor
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_factor_enreal_stopped_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T04:25:48.12036+00:00
-- url     : https://prove2.me/theorems/3ce91e20-486e-4e51-8a72-adc4efbdb861
-- title:
--   ENNReal lower-killed stopped reward factor
-- statement:
--   At the lower-killed first upward passage of a spectrally negative Levy path, the discounted ENNReal reward of the post-passage increments factors into the stopped discount mass times the unstopped reward expectation.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem Kyprianou.Ch08.StageB.p2m87_qpos_factor_enreal_stopped_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F)
    (lower upper : ℝ) (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    (∫⁻ ω, if U ω < L ω then discount ((U ω).toNNReal) *
        reward (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω)
      else 0 ∂P) =
      (∫⁻ ω, if U ω < L ω then discount ((U ω).toNNReal) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)
:= by
  sorry
