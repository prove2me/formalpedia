-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isRestricted_extend
-- name    : GroundTheory.Automorphic.RestrictedTensor.isRestricted_extend
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:50.728776+00:00
-- url     : https://prove2.me/theorems/54adaf0b-8bc4-469d-988e-ff9ea8eb201d
-- title:
--   Restricted Tensor: is Restricted extend
-- statement:
--   The Restricted Tensor construction uses the is Restricted extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L286-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L286-L292

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

theorem GroundTheory.Automorphic.RestrictedTensor.isRestricted_extend (ξ : ∀ v, V v) (T : Finset ι) (y : ∀ v : T, V v) :
    IsRestricted ξ (extend ξ T y) := by sorry
