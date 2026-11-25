-- Prove2me | Theorems.Thm_GlobalTheory_BCT_DimFac_exists_split
-- name    : GlobalTheory.BCT.DimFac.exists_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:21:18.531385+00:00
-- url     : https://prove2.me/theorems/c6e8020d-950b-4c8f-aea0-2d9a3b071f7a
-- title:
--   Dim Fac: exists split
-- statement:
--   The Dim Fac construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L90-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L90-L142

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

theorem GlobalTheory.BCT.DimFac.exists_split {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible) {σ : Representation ℂ Γ W}
    (hσ : σ.IsIrreducible) (hs : ∀ T : End ℂ W, (∀ g, T * σ g = σ g * T) → ∃ c : ℂ, T = c • 1) {e : Γ →* Γ}
    (he : ∀ g, e (e g) = e g) (hc : ∀ g y, Commute ((e g)⁻¹ * g) (e y))
    {f : W →ₗ[ℂ] V} (hf0 : f ≠ 0) (hf : ∀ g x, f (σ g x) = ρ (e g) (f x)) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (τ : Representation ℂ Γ M) (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V),
      (∀ g, τ (e g) = 1) ∧ ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t) := by sorry
