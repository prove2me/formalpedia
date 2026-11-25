-- Prove2me | Theorems.Thm_GlobalTheory_BCT_DimFac_irred_right
-- name    : GlobalTheory.BCT.DimFac.irred_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:32.14827+00:00
-- url     : https://prove2.me/theorems/b5d47aee-86a7-4674-ad37-0b9787e42cdf
-- title:
--   Dim Fac: irred right
-- statement:
--   The Dim Fac construction uses the irred right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L151-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L151-L179

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

theorem GlobalTheory.BCT.DimFac.irred_right {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible) {σ : Representation ℂ Γ W}
    {τ : Representation ℂ Γ M} (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V) (hΦ : ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t)) :
    τ.IsIrreducible := by sorry
