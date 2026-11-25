-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_rankOne_simple
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_rankOne_simple
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:00:46.954556+00:00
-- url     : https://prove2.me/theorems/9e87242f-376f-4b4f-9b48-720d5882dcfe
-- title:
--   Restricted Tensor: exists rank One simple
-- statement:
--   The Restricted Tensor construction uses the exists rank One simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L20-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L20-L42

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

theorem GroundTheory.Automorphic.RestrictedTensor.exists_rankOne_simple (T : Set (End ℂ M)) [Nontrivial M] :
    ∃ (N : Submodule ℂ M) (hN : IsStable T N), N ≠ ⊥ ∧ IsSimpleUnder (restrictSet T N hN) ∧
      ∃ p ∈ Algebra.adjoin ℂ T, ∃ n₀ ∈ N, n₀ ≠ 0 ∧ p n₀ = n₀ ∧ ∀ x ∈ N, ∃ c : ℂ, p x = c • n₀ := by sorry
