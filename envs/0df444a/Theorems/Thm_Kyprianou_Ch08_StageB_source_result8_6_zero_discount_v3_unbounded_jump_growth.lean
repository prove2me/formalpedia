-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_jump_growth
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_jump_growth
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:37:00.574796+00:00
-- url     : https://prove2.me/theorems/aab5c1b8-18f0-4c39-a24c-e6f707fa4287
-- title:
--   Infinite first moment gives divergent compensated jump growth
-- statement:
--   If a Levy measure has infinite first absolute moment on (-1,0), the normalized compensated negative-jump integral eventually exceeds every real constant.
-- source:
--   Measure-generic zero-Gaussian branch extracted from the unbounded-variation Lemma 8.6 proof using the Proved compensated-jump divergence and monotonicity theorems.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_negative_compensated_real_integral_tendsto_atTop
import Theorems.Thm_AvramDividend_Classical_negative_compensated_integral_mono
set_option autoImplicit false
open MeasureTheory Filter Set
noncomputable section

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_jump_growth
    (μ : Measure ℝ) (hμ : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂μ) = ⊤) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧ ∀ θ : ℝ, β ≤ θ →
      C < ∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ := by
  sorry
