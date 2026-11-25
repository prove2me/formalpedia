-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_fst_of_equiv
-- name    : GroundTheory.Automorphic.RestrictedTensor.nonempty_equiv_fst_of_equiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:27:06.653206+00:00
-- url     : https://prove2.me/theorems/0ec17747-22fd-434d-ac2e-72b5341692f5
-- title:
--   Restricted Tensor: nonempty equiv fst of equiv
-- statement:
--   The Restricted Tensor construction uses the nonempty equiv fst of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactorUnique.lean#L98-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactorUnique.lean#L98-L125

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set TensorProduct
open scoped TensorProduct
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
  {V₁ V₂ V₁' V₂' : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₁'] [Module ℂ V₁'] [AddCommGroup V₂'] [Module ℂ V₂']
variable {π₁ : Representation ℂ M₁ V₁} {π₂ : Representation ℂ M₂ V₂}
  {π₁' : Representation ℂ M₁ V₁'} {π₂' : Representation ℂ M₂ V₂'}

theorem GroundTheory.Automorphic.RestrictedTensor.nonempty_equiv_fst_of_equiv (h₁ : π₁.IsIrreducible) (h₂ : π₂.IsIrreducible)
    (h₁' : π₁'.IsIrreducible) (Φ : (outerTensor π₁ π₂).Equiv (outerTensor π₁' π₂')) :
    Nonempty (π₁.Equiv π₁') := by sorry
