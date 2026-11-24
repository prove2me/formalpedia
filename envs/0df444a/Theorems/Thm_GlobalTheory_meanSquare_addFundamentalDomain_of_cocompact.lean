-- Prove2me | Theorems.Thm_GlobalTheory_meanSquare_addFundamentalDomain_of_cocompact
-- name    : GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:52:16.302362+00:00
-- url     : https://prove2.me/theorems/e6e349ab-baa1-4c23-9405-afddbc083676
-- title:
--   Global Theory: mean Square add Fundamental Domain of cocompact
-- statement:
--   The Global Theory construction uses the mean Square add Fundamental Domain of cocompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MeanSquareAddFundamentalDomainOfCocompact.lean#L25-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MeanSquareAddFundamentalDomainOfCocompact.lean#L25-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MeanSquareAddFundamentalDomainOfCocompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory

theorem GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) → (∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1) ∧ ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖) → ∃ N : NNReal, ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = μ 𝓕 * N ∧ ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ = (μ 𝓕).toReal * N := by sorry
