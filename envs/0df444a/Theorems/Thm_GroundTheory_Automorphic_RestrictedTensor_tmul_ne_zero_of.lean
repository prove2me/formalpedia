-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_tmul_ne_zero_of
-- name    : GroundTheory.Automorphic.RestrictedTensor.tmul_ne_zero_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:14:16.445402+00:00
-- url     : https://prove2.me/theorems/e3f6d025-6bb4-421d-9468-0e933066b459
-- title:
--   Restricted Tensor: tmul ne zero of
-- statement:
--   The Restricted Tensor construction uses the tmul ne zero of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactorUnique.lean#L85-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactorUnique.lean#L85-L93

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

theorem GroundTheory.Automorphic.RestrictedTensor.tmul_ne_zero_of {x : V₁} {y : V₂} (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by sorry
