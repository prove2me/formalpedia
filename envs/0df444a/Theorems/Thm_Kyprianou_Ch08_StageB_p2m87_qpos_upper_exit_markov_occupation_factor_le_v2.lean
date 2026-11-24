-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_upper_exit_markov_occupation_factor_le_v2
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_upper_exit_markov_occupation_factor_le_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T02:42:35.543654+00:00
-- url     : https://prove2.me/theorems/3c0fe346-0586-4423-b9db-b1744ecef767
-- title:
--   Upper-exit strong-Markov factor for positive-discount killed occupation, non-strict time form
-- statement:
--   For a spectrally negative Levy source with 0<q, 0<a, 0<=x<=a and any measurable state set A, the discounted occupation at times t with tauPlus<=t<tauMinus factors into the discounted upper-before-lower exit expectation times the discounted killed half-line occupation restarted at level a. The non-strict upper-time form makes the deterministic time split exact.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m87_qpos_upper_exit_markov_occupation_factor_le_v2 :
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
              tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) =
        ENNReal.ofReal (upBeforeDownExpectation P D.X q x a) *
          (∫⁻ t : ℝ≥0,
            ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
              P {ω | (t : WithTop ℝ≥0) <
                tauMinus (shifted D.X a) 0 ω ∧
                shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue) := by
  sorry
