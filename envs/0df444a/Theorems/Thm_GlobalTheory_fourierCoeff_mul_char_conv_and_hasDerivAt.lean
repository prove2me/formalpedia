-- Prove2me | Theorems.Thm_GlobalTheory_fourierCoeff_mul_char_conv_and_hasDerivAt
-- name    : GlobalTheory.fourierCoeff_mul_char_conv_and_hasDerivAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:53:33.742537+00:00
-- url     : https://prove2.me/theorems/323a8803-42a8-48f7-b6ec-9ce6439346e3
-- title:
--   Global Theory: fourier Coeff mul char conv and has Deriv At
-- statement:
--   The Global Theory construction uses the fourier Coeff mul char conv and has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierCoeffMulCharConvAndHasDerivAt.lean#L22-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierCoeffMulCharConvAndHasDerivAt.lean#L22-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MeanSquareAddFundamentalDomainOfCocompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierCoeffMulCharConvAndHasDerivAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open MeasureTheory
open scoped Pointwise

theorem GlobalTheory.fourierCoeff_mul_char_conv_and_hasDerivAt :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ χ : G → ℂ, Continuous χ → (∀ x y, χ (x + y) = χ x * χ y) → (∀ x, ‖χ x‖ = 1) → (∀ γ ∈ Γ, χ γ = 1) → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ z, (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ z = ∫ y in 𝓕, Φ (z + y) * starRingEnd ℂ (χ y) ∂μ) ∧ ∀ (L : ℝ →+ G) (Φ' : G → ℂ), Continuous Φ' → (∀ γ ∈ Γ, ∀ x, Φ' (γ + x) = Φ' x) → (∀ x, HasDerivAt (fun t : ℝ => Φ (x + L t)) (Φ' x) 0) → ∀ x, HasDerivAt (fun t : ℝ => (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ (x + L t)) ((∫ y in 𝓕, Φ' y * starRingEnd ℂ (χ y) ∂μ) * χ x) 0 := by sorry
