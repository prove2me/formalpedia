-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_finiteEmbed_injective
-- name    : GroundTheory.Automorphic.RestrictedTensor.finiteEmbed_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:54:01.927493+00:00
-- url     : https://prove2.me/theorems/55e80ac4-598e-42aa-bccf-f443b174cfa7
-- title:
--   Restricted Tensor: finite Embed injective
-- statement:
--   The Restricted Tensor construction uses the finite Embed injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L319-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L319-L352

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
variable [DecidableEq ι]

theorem GroundTheory.Automorphic.RestrictedTensor.finiteEmbed_injective {ξ : ∀ v, V v} {T : Finset ι} (hξ : ∀ v ∉ T, ξ v ≠ 0) :
    Injective (finiteEmbed ξ T) := by sorry
