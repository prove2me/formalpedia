-- Prove2me | Theorems.Thm_GlobalTheory_T_ae_exists_pairGroup_smul_mem_sheared_domain
-- name    : GlobalTheory.T.ae_exists_pairGroup_smul_mem_sheared_domain
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:32.499195+00:00
-- url     : https://prove2.me/theorems/e92733a5-1c07-4f59-a429-a07b7077b1bd
-- title:
--   T: ae exists pair Group smul mem sheared domain
-- statement:
--   The T construction uses the ae exists pair Group smul mem sheared domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AeExistsPairGroupSmulMemShearedDomainStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AeExistsPairGroupSmulMemShearedDomainStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AeExistsPairGroupSmulMemShearedDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AeExistsPairGroupSmulMemShearedDomainStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ae_exists_pairGroup_smul_mem_sheared_domain : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → ∀ᵐ p ∂((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)), ∃ g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN, g • p ∈ GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕) := by sorry
