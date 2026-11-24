-- Prove2me | Theorems.Thm_GlobalTheory_T_integral_mul_convolution_eq_alt
-- name    : GlobalTheory.T.integral_mul_convolution_eq_alt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:46:56.30837+00:00
-- url     : https://prove2.me/theorems/fbfa2b51-19d3-45a9-8112-19b204f753e2
-- title:
--   T: integral mul convolution eq alt
-- statement:
--   The T construction uses the integral mul convolution eq alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulConvolutionEqStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulConvolutionEqStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulConvolutionEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulConvolutionEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integral_mul_convolution_eq_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∀ κ a : H → ℂ, Continuous κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → ∀ f : H → ℂ, Continuous f → ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by sorry
