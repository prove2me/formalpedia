-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_restrictedLift_apply_of
-- name    : GroundTheory.Automorphic.RestrictedTensor.restrictedLift_apply_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:56.371256+00:00
-- url     : https://prove2.me/theorems/2d907c57-a7b5-46ac-a4a9-3e0c396d8bed
-- title:
--   Restricted Tensor: restricted Lift apply of
-- statement:
--   The Restricted Tensor construction uses the restricted Lift apply of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L204-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L204-L209

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

theorem GroundTheory.Automorphic.RestrictedTensor.restrictedLift_apply_of {ξ : ∀ v, V v} {T : Finset ι} {l : ∀ v, Dual ℂ (V v)}
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} (f : MultilinearMap ℂ (fun v : T => V v) N)
    {x : ∀ v, V v} (hx : IsRestricted ξ x) :
    restrictedLift ξ T l hl f x = (∏ᶠ v, weight T l x v) • f (fun v => x v) := by sorry
