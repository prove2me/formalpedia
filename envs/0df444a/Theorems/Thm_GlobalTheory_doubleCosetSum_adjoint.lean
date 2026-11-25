-- Prove2me | Theorems.Thm_GlobalTheory_doubleCosetSum_adjoint
-- name    : GlobalTheory.doubleCosetSum_adjoint
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:33.777805+00:00
-- url     : https://prove2.me/theorems/143dd12b-7fc5-4b61-baff-3341eb422c2d
-- title:
--   Global Theory: double Coset Sum adjoint
-- statement:
--   The Global Theory construction uses the double Coset Sum adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L60-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L60-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSumFundamentalDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.DoubleCosetAdjoint

theorem GlobalTheory.doubleCosetSum_adjoint : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K : Subgroup H) [Countable Γ] (𝓕 : Set H) (x : H) (A A' : Finset H) (F F' : H → ℂ), IsFundamentalDomain Γ 𝓕 μ → (∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) → (∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) → A.card = A'.card → Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ γ ∈ Γ, ∀ h, F' (γ * h) = F' h) → (∀ k ∈ K, ∀ h, F (h * k) = F h) → (∀ k ∈ K, ∀ h, F' (h * k) = F' h) → IntegrableOn (fun h => star (F h) * F h) 𝓕 μ → IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ → ∫ h in 𝓕, star (∑ a ∈ A, F (h * a)) * F' h ∂μ = ∫ h in 𝓕, star (F h) * ∑ a ∈ A', F' (h * a) ∂μ := by sorry
