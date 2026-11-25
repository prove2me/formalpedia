-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_tensorForm_tmul
-- name    : GroundTheory.Automorphic.RestrictedTensor.tensorForm_tmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:41.456018+00:00
-- url     : https://prove2.me/theorems/6f625bb0-54f9-4a8e-aa79-a3c637203ba0
-- title:
--   Restricted Tensor: tensor Form tmul
-- statement:
--   The Restricted Tensor construction uses the tensor Form tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactor.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactor.lean#L41-L44

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
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
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ρ₁ : Representation ℂ M₁ V} {ρ₂ : Representation ℂ M₂ V}
  {hcomm : ∀ a b, ρ₁ a * ρ₂ b = ρ₂ b * ρ₁ a} {e₁ e₂ : End ℂ V}

theorem GroundTheory.Automorphic.RestrictedTensor.tensorForm_tmul {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] (φ : Dual ℂ V₁) (ψ : Dual ℂ V₂) (x : V₁) (y : V₂) :
    tensorForm φ ψ (x ⊗ₜ y) = φ x * ψ y := by sorry
