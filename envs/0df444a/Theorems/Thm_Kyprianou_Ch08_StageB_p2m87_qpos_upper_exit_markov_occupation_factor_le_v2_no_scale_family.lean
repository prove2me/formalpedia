-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_upper_exit_markov_occupation_factor_le_v2_no_scale_family
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_upper_exit_markov_occupation_factor_le_v2_no_scale_family
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T03:52:04.888326+00:00
-- url     : https://prove2.me/theorems/d553554e-c395-4944-937b-497cffee94ee
-- title:
--   Upper-exit Markov occupation factor without the unused scale-family parameter
-- statement:
--   The upper-before-lower exit factorization of the discounted killed occupation holds for every spectrally negative source with a matching Laplace exponent, without assuming a source scale family; this isolates the substantive transfer and Markov factorization from the parent's unused scale-family binder.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m87_qpos_upper_exit_markov_occupation_factor_le_v2_no_scale_family :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
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
