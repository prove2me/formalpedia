-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_prodRep_apply
-- name    : GroundTheory.Automorphic.RestrictedTensor.prodRep_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:17.8978+00:00
-- url     : https://prove2.me/theorems/68c53f1a-4c6f-495c-bcff-e168f1bfa6b0
-- title:
--   Restricted Tensor: prod Rep apply
-- statement:
--   The Restricted Tensor construction uses the prod Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactor.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactor.lean#L28-L30

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

theorem GroundTheory.Automorphic.RestrictedTensor.prodRep_apply (ρ₁ : Representation ℂ M₁ V) (ρ₂ : Representation ℂ M₂ V) (hcomm)
    (p : M₁ × M₂) (v : V) : prodRep ρ₁ ρ₂ hcomm p v = ρ₁ p.1 (ρ₂ p.2 v) := by sorry
