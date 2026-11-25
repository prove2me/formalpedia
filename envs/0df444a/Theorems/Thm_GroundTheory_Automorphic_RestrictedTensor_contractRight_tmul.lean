-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractRight_tmul
-- name    : GroundTheory.Automorphic.RestrictedTensor.contractRight_tmul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:15:40.229804+00:00
-- url     : https://prove2.me/theorems/23bc3cdd-df90-45e4-8911-9e7073f30694
-- title:
--   Restricted Tensor: contract Right tmul
-- statement:
--   The Restricted Tensor construction uses the contract Right tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactorUnique.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactorUnique.lean#L24-L26

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

theorem GroundTheory.Automorphic.RestrictedTensor.contractRight_tmul (l : Dual ℂ V₂) (x : V₁) (y : V₂) :
    contractRight l (x ⊗ₜ y) = l y • x := by sorry
