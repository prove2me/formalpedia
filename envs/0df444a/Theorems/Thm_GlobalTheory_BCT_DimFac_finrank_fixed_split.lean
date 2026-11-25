-- Prove2me | Theorems.Thm_GlobalTheory_BCT_DimFac_finrank_fixed_split
-- name    : GlobalTheory.BCT.DimFac.finrank_fixed_split
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:20.788087+00:00
-- url     : https://prove2.me/theorems/4ac793d6-d4cd-4715-b039-99dde6fc21ac
-- title:
--   Dim Fac: finrank fixed split
-- statement:
--   The Dim Fac construction uses the finrank fixed split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L201-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L201-L237

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.BCT.DimFac.finrank_fixed_split {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ M}
    (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V) (hΦ : ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t)) {e : Γ →* Γ}
    (hσ : ∀ g, σ (e g) = σ g) (hτ : ∀ g, τ (e g) = 1) {L : Subgroup Γ} (hL : ∀ g ∈ L, e g ∈ L) :
    finrank ℂ (fixed ρ L) = finrank ℂ (fixed σ L) * finrank ℂ (fixed τ L) := by sorry
