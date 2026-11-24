-- Prove2me | Theorems.Thm_GlobalTheory_integral_mul_convolution_eq
-- name    : GlobalTheory.integral_mul_convolution_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:56:01.115623+00:00
-- url     : https://prove2.me/theorems/d43126db-71d4-47a9-80db-766111374d2b
-- title:
--   Global Theory: integral mul convolution eq
-- statement:
--   The Global Theory construction uses the integral mul convolution eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulConvolutionEq.lean#L6-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulConvolutionEq.lean#L6-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulConvolutionEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Pointwise
open GlobalTheory

theorem GlobalTheory.integral_mul_convolution_eq (H : Type) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) (hμ : μ.IsHaarMeasure)
    (K : Set H) (hK : IsCompact K) (κ a : H → ℂ) (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (ha : Measurable a) (hai : Integrable a μ)
    (haK : ∀ x ∉ K, a x = 0) (f : H → ℂ) (hf : Continuous f) :
    ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by sorry
