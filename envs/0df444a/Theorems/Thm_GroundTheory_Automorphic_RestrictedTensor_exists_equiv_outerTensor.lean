-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_equiv_outerTensor
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_equiv_outerTensor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:11:45.040802+00:00
-- url     : https://prove2.me/theorems/a31c9e1c-d604-45e4-bcd7-4c186e254c9a
-- title:
--   Restricted Tensor: exists equiv outer Tensor
-- statement:
--   The Restricted Tensor construction uses the exists equiv outer Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactor.lean#L46-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactor.lean#L46-L360

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

theorem GroundTheory.Automorphic.RestrictedTensor.exists_equiv_outerTensor (hirr : (prodRep ρ₁ ρ₂ hcomm).IsIrreducible)
    (he₁ : IsWinProj ρ₁ e₁) (he₂ : IsWinProj ρ₂ e₂) (he₁₂ : ∀ b, e₁ * ρ₂ b = ρ₂ b * e₁)
    (he₂₁ : ∀ a, e₂ * ρ₁ a = ρ₁ a * e₂) (hee : e₁ * e₂ = e₂ * e₁)
    [FiniteDimensional ℂ (LinearMap.range (e₁ * e₂))] (hne : LinearMap.range (e₁ * e₂) ≠ ⊥) :
    ∃ (N₁ N₂ : Submodule ℂ V), N₁ ≤ LinearMap.range (e₁ * e₂) ∧ N₂ ≤ LinearMap.range (e₁ * e₂) ∧
      N₁ ≠ ⊥ ∧ N₂ ≠ ⊥ ∧ (∀ a, ∀ n ∈ N₁, e₁ (ρ₁ a n) ∈ N₁) ∧ (∀ b, ∀ n ∈ N₂, e₂ (ρ₂ b n) ∈ N₂) ∧
      (mGenQuotRep ρ₁ e₁ N₁).IsIrreducible ∧ (mGenQuotRep ρ₂ e₂ N₂).IsIrreducible ∧
      ((∀ T : End ℂ ((mGenSubrep ρ₂ N₂).toSubmodule ⧸ mGenKernel ρ₂ e₂ N₂),
          (∀ b, T * mGenQuotRep ρ₂ e₂ N₂ b = mGenQuotRep ρ₂ e₂ N₂ b * T) → ∃ c : ℂ, T = c • 1) →
        Nonempty ((prodRep ρ₁ ρ₂ hcomm).Equiv
          (outerTensor (mGenQuotRep ρ₁ e₁ N₁) (mGenQuotRep ρ₂ e₂ N₂)))) := by sorry
