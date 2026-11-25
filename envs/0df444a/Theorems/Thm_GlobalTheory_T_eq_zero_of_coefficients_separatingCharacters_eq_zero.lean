-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_zero_of_coefficients_separatingCharacters_eq_zero
-- name    : GlobalTheory.T.eq_zero_of_coefficients_separatingCharacters_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:53.575924+00:00
-- url     : https://prove2.me/theorems/60c38a10-769e-53d7-add9-955bf0860085
-- title:
--   T: eq zero of coefficients separating Characters eq zero
-- statement:
--   The T construction uses the eq zero of coefficients separating Characters eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfCoefficientsSeparatingCharactersEqZeroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfCoefficientsSeparatingCharactersEqZeroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCoefficientsSeparatingCharactersEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCoefficientsSeparatingCharactersEqZeroStatement
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

theorem GlobalTheory.T.eq_zero_of_coefficients_separatingCharacters_eq_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ a, ∫ x in 𝓕, χ a x * Φ x ∂μ = 0) → Φ = 0 := by sorry
