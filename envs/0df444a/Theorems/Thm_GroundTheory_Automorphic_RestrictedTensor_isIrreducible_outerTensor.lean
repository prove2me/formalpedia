-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isIrreducible_outerTensor
-- name    : GroundTheory.Automorphic.RestrictedTensor.isIrreducible_outerTensor
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:43.711415+00:00
-- url     : https://prove2.me/theorems/1e2553da-effb-4207-8748-2b62d9faf454
-- title:
--   Restricted Tensor: is Irreducible outer Tensor
-- statement:
--   The Restricted Tensor construction uses the is Irreducible outer Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/OuterTensor.lean#L85-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/OuterTensor.lean#L85-L193

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor
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
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]

theorem GroundTheory.Automorphic.RestrictedTensor.isIrreducible_outerTensor {ρ₁ : Representation ℂ M₁ V₁} {ρ₂ : Representation ℂ M₂ V₂}
    (hirr₁ : ρ₁.IsIrreducible) (hirr₂ : ρ₂.IsIrreducible)
    (hschur : ∀ T : End ℂ V₂, (∀ m, T * ρ₂ m = ρ₂ m * T) → ∃ c : ℂ, T = c • 1) :
    (outerTensor ρ₁ ρ₂).IsIrreducible := by sorry
