-- Prove2me | Theorems.Thm_GlobalTheory_BCT_DimFac_HasComp_exists_op
-- name    : GlobalTheory.BCT.DimFac.HasComp.exists_op
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:43.8553+00:00
-- url     : https://prove2.me/theorems/21c68c30-8c26-4fa9-96c9-dab9e4cccb9a
-- title:
--   Has Comp: exists op
-- statement:
--   The Has Comp construction uses the exists op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L290-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L290-L317

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

theorem GlobalTheory.BCT.DimFac.HasComp.exists_op {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible) {e : Γ →* Γ}
    (he : ∀ g, e (e g) = e g) (hc : ∀ g y, Commute ((e g)⁻¹ * g) (e y)) {L : Subgroup Γ} (h : HasComp ρ e L 1) :
    ∃ P : V →ₗ[ℂ] V, (∀ g, e g = 1 → ∀ v, P (ρ g v) = ρ g (P v)) ∧
      ∀ v, (∀ g ∈ L, ρ (e g) v = v) → P v = v ∧ ∀ y, ∃ c : ℂ, P (ρ (e y) v) = c • v := by sorry
