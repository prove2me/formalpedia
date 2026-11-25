-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractLeft_outerTensor
-- name    : GroundTheory.Automorphic.RestrictedTensor.contractLeft_outerTensor
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:16:09.866529+00:00
-- url     : https://prove2.me/theorems/aa35de24-c60b-4664-8c23-093f11cf3ca1
-- title:
--   Restricted Tensor: contract Left outer Tensor
-- statement:
--   The Restricted Tensor construction uses the contract Left outer Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactorUnique.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactorUnique.lean#L77-L83

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

theorem GroundTheory.Automorphic.RestrictedTensor.contractLeft_outerTensor (π₁ : Representation ℂ M₁ V₁) (π₂ : Representation ℂ M₂ V₂)
    (l : Dual ℂ V₁) (b : M₂) (z : V₁ ⊗[ℂ] V₂) :
    contractLeft l (outerTensor π₁ π₂ (1, b) z) = π₂ b (contractLeft l z) := by sorry
