-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_interval_occupation_halfline_add_split
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_interval_occupation_halfline_add_split
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:35:08.70369+00:00
-- url     : https://prove2.me/theorems/e337c740-9494-4b38-b735-4860dc1ede52
-- title:
--   Positive-discount killed interval occupation splits at the upper exit
-- statement:
--   For 0<q and 0<=x<=a, the discounted killed half-line occupation started at x equals the occupation killed at both endpoints plus the q-scale upper-before-lower exit ratio times the discounted killed half-line occupation started at a. This is the strong-Markov half of the positive-discount interval occupation bridge.
-- source:
--   Source-faithful split of exact bridge target dd94395e-5a1b-4371-8a44-53bb6ca85201 at pinned revision 0df444a360eaa60ab8c11dca51a86af692955474

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m87_qpos_interval_occupation_halfline_add_split :
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
        ENNReal.ofReal (W q x / W q a) *
          (∫⁻ t : ℝ≥0,
            ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
              P {ω | (t : WithTop ℝ≥0) <
                tauMinus (shifted D.X a) 0 ω ∧
                shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue) := by sorry
