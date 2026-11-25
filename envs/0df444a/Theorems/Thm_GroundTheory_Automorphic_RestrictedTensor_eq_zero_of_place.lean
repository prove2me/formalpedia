-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_place
-- name    : GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_place
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:31.404546+00:00
-- url     : https://prove2.me/theorems/1b4f13e5-7805-4776-935f-6f545cd5955d
-- title:
--   Restricted Tensor: eq zero of place
-- statement:
--   The Restricted Tensor construction uses the eq zero of place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L52-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L52-L72

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

theorem GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_place (hsimple : IsSimpleUnder (⋃ v, T v))
    (hcomm : ∀ v w, v ≠ w → ∀ a ∈ T v, ∀ b ∈ T w, Commute a b) (v : ι) {N : Submodule ℂ M}
    (hN : N ≠ ⊥) (hNs : IsStable (T v) N) {a : End ℂ M} (ha : a ∈ Algebra.adjoin ℂ (T v))
    (h0 : ∀ x ∈ N, a x = 0) : a = 0 := by sorry
