-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_adjoin
-- name    : GroundTheory.Automorphic.RestrictedTensor.commute_adjoin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:43.738569+00:00
-- url     : https://prove2.me/theorems/62cac055-76d1-402b-bae0-feefd72b6d3a
-- title:
--   Restricted Tensor: commute adjoin
-- statement:
--   The Restricted Tensor construction uses the commute adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L46-L50

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
variable {ι : Type*} {T : ι → Set (End ℂ M)}

theorem GroundTheory.Automorphic.RestrictedTensor.commute_adjoin (hcomm : ∀ v w, v ≠ w → ∀ a ∈ T v, ∀ b ∈ T w, Commute a b)
    {v w : ι} (hvw : v ≠ w) {a b : End ℂ M} (ha : a ∈ Algebra.adjoin ℂ (T v))
    (hb : b ∈ Algebra.adjoin ℂ (T w)) : Commute a b := by sorry
