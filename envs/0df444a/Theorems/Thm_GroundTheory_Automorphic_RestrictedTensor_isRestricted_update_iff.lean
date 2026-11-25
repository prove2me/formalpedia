-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isRestricted_update_iff
-- name    : GroundTheory.Automorphic.RestrictedTensor.isRestricted_update_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:04.013635+00:00
-- url     : https://prove2.me/theorems/aa8864a8-75ce-4ccd-9a02-e2bbead1b2d5
-- title:
--   Restricted Tensor: is Restricted update iff
-- statement:
--   The Restricted Tensor construction uses the is Restricted update iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L35-L39

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

theorem GroundTheory.Automorphic.RestrictedTensor.isRestricted_update_iff [DecidableEq ι] {ξ x : ∀ v, V v} {i : ι} {a : V i} :
    IsRestricted ξ (Function.update x i a) ↔ IsRestricted ξ x := by sorry
