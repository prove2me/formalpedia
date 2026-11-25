-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_finprod_eq_mul_weight
-- name    : GroundTheory.Automorphic.RestrictedTensor.finprod_eq_mul_weight
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:01.303541+00:00
-- url     : https://prove2.me/theorems/277dde6b-99ab-4d2f-8c7a-bb49f0dbd1b6
-- title:
--   Restricted Tensor: finprod eq mul weight
-- statement:
--   The Restricted Tensor construction uses the finprod eq mul weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L243-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L243-L260

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
variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem GroundTheory.Automorphic.RestrictedTensor.finprod_eq_mul_weight {ξ x : ∀ v, V v} (hx : IsRestricted ξ x) {l : ∀ v, Dual ℂ (V v)}
    (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) (v : ι) :
    ∏ᶠ w, l w (x w) = l v (x v) * ∏ᶠ w, weight {v} l x w := by sorry
