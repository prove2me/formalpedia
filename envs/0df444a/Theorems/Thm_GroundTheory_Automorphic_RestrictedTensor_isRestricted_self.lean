-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isRestricted_self
-- name    : GroundTheory.Automorphic.RestrictedTensor.isRestricted_self
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:34:18.737388+00:00
-- url     : https://prove2.me/theorems/6a71d01d-059f-46e6-8e0f-793dccf7f86b
-- title:
--   Restricted Tensor: is Restricted self
-- statement:
--   The Restricted Tensor construction uses the is Restricted self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L23-L24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
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
open PiTensorProduct Filter Function Module Set
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

theorem GroundTheory.Automorphic.RestrictedTensor.isRestricted_self (ξ : ∀ v, V v) : IsRestricted ξ ξ := by sorry
