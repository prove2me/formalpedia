-- Prove2me | Theorems.Thm_GlobalTheory_exists_isAddHaarMeasure_isAddFundamentalDomain_preimage
-- name    : GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:58:51.531799+00:00
-- url     : https://prove2.me/theorems/7266b110-3285-4be8-b4dc-1ff4796a59ae
-- title:
--   Global Theory: exists is Add Haar Measure is Add Fundamental Domain preimage
-- statement:
--   The Global Theory construction uses the exists is Add Haar Measure is Add Fundamental Domain preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIsAddHaarMeasureIsAddFundamentalDomainPrei.lean#L6-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIsAddHaarMeasureIsAddFundamentalDomainPrei.lean#L6-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIsAddHaarMeasureIsAddFundamentalDomainPrei
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

theorem GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (e : G ≃+ H), Continuous e → Continuous e.symm → ∀ (Γ : AddSubgroup G) (Λ : AddSubgroup H), (∀ x, e x ∈ Λ ↔ x ∈ Γ) → ∀ (μ : Measure H) (𝓕 : Set H), μ.IsAddHaarMeasure → IsAddFundamentalDomain Λ 𝓕 μ → ∃ ν : Measure G, ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ (e ⁻¹' 𝓕) ν ∧ ∀ φ : H → ℝ, ∫ w in e ⁻¹' 𝓕, φ (e w) ∂ν = ∫ w in 𝓕, φ w ∂μ := by sorry
