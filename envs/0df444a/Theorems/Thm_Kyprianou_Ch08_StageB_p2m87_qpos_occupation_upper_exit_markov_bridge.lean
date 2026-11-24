-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_occupation_upper_exit_markov_bridge
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_occupation_upper_exit_markov_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T01:08:44.997018+00:00
-- url     : https://prove2.me/theorems/d1876b4f-762e-4e43-870a-6d628160e2e4
-- title:
--   Positive-discount occupation split at upper passage
-- statement:
--   Strong Markov split of the discounted killed half-line occupation measure at the first upper passage before the lower passage. The post-passage occupation contribution is the discounted upper-before-lower exit expectation times the killed half-line occupation measure restarted from the upper level. This isolates the stochastic strong-Markov and Tonelli obligations from the scale-function ratio proved in source_result81_upper_exit_ratio.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m87_qpos_occupation_upper_exit_markov_bridge :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        (∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              tauMinus (shifted D.X x) 0 ω ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) =
        (∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              min (tauMinus (shifted D.X x) 0 ω)
                (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) +
        ENNReal.ofReal (upBeforeDownExpectation P D.X q x a) *
          (∫⁻ t : ℝ≥0,
            ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
              P {ω | (t : WithTop ℝ≥0) <
                tauMinus (shifted D.X a) 0 ω ∧
                shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue) := by sorry
