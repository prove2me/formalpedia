-- Prove2me | Theorems.Thm_GlobalTheory_CosetAvg_sum_translates_eq_avg
-- name    : GlobalTheory.CosetAvg.sum_translates_eq_avg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:57.73469+00:00
-- url     : https://prove2.me/theorems/276ffcda-3bba-4e70-8352-7475f4dae2e5
-- title:
--   Coset Avg: sum translates eq avg
-- statement:
--   The Coset Avg construction uses the sum translates eq avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumTranslatesEqDoubleCosetAverage.lean#L54-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumTranslatesEqDoubleCosetAverage.lean#L54-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTranslatesEqDoubleCosetAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.CosetAvg
open MulAction

theorem GlobalTheory.CosetAvg.sum_translates_eq_avg : ∀ {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : G →* Module.End ℂ M) (K : Subgroup G) {ι : Type} (s : Finset ι) (a : ι → G) (R : ι → Finset G) (w : ι → M), (∀ i ∈ s, (∀ γ ∈ R i, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * a i * k₂) ∧ ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a i * k₂) → ∃! γ, γ ∈ R i ∧ γ⁻¹ * x ∈ K) → (∀ i ∈ s, ∀ k ∈ K, ρ k (w i) = w i) → (∀ k ∈ K, ρ k (∑ i ∈ s, ρ (a i) (w i)) = ∑ i ∈ s, ρ (a i) (w i)) → ∑ i ∈ s, ρ (a i) (w i) = ∑ i ∈ s, ((R i).card : ℂ)⁻¹ • ∑ γ ∈ R i, ρ γ (w i) := by sorry
