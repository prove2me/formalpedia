-- Prove2me | Theorems.Thm_GlobalTheory_BCT_DimFac_map_right_of_fixed
-- name    : GlobalTheory.BCT.DimFac.map_right_of_fixed
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:03.332673+00:00
-- url     : https://prove2.me/theorems/cac3fb1c-3df7-454b-9ee5-fb62e856e56d
-- title:
--   Dim Fac: map right of fixed
-- statement:
--   The Dim Fac construction uses the map right of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L191-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L191-L199

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

theorem GlobalTheory.BCT.DimFac.map_right_of_fixed {τ : Representation ℂ Γ M} {L : Subgroup Γ} {t : W ⊗[ℂ] M}
    (ht : ∀ g ∈ L, TensorProduct.map LinearMap.id (τ g) t = t) (p : M →ₗ[ℂ] M) (hp : ∀ x ∈ fixed τ L, p x = x) :
    TensorProduct.map LinearMap.id p t = t := by sorry
