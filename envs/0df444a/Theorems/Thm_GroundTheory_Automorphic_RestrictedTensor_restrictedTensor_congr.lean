-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_restrictedTensor_congr
-- name    : GroundTheory.Automorphic.RestrictedTensor.restrictedTensor_congr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:30.534539+00:00
-- url     : https://prove2.me/theorems/cb4e1d7a-70c5-42d0-ba85-c854582d7ebc
-- title:
--   Restricted Tensor: restricted Tensor congr
-- statement:
--   The Restricted Tensor construction uses the restricted Tensor congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L48-L57

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

theorem GroundTheory.Automorphic.RestrictedTensor.restrictedTensor_congr {ξ ξ' : ∀ v, V v} (h : ∀ᶠ v in cofinite, ξ v = ξ' v) :
    restrictedTensor ξ = restrictedTensor ξ' := by sorry
