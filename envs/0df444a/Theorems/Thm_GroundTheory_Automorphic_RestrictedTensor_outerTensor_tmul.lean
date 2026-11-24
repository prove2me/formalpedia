-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_outerTensor_tmul
-- name    : GroundTheory.Automorphic.RestrictedTensor.outerTensor_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:49.50491+00:00
-- url     : https://prove2.me/theorems/bc3651a3-8e12-4ad7-8197-3fde24ff8dc8
-- title:
--   Restricted Tensor: outer Tensor tmul
-- statement:
--   The Restricted Tensor construction uses the outer Tensor tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/OuterTensor.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/OuterTensor.lean#L37-L40

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

theorem GroundTheory.Automorphic.RestrictedTensor.outerTensor_tmul (ρ₁ : Representation ℂ M₁ V₁) (ρ₂ : Representation ℂ M₂ V₂)
    (p : M₁ × M₂) (a : V₁) (b : V₂) :
    outerTensor ρ₁ ρ₂ p (a ⊗ₜ b) = ρ₁ p.1 a ⊗ₜ ρ₂ p.2 b := by sorry
