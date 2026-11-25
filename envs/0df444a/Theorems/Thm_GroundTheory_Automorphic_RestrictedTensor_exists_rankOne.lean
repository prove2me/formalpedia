-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_rankOne
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_rankOne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:19.986203+00:00
-- url     : https://prove2.me/theorems/732f6aca-e9fc-4fc1-ad49-e2bdad23725d
-- title:
--   Restricted Tensor: exists rank One
-- statement:
--   The Restricted Tensor construction uses the exists rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L218-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L218-L240

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
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
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable [FiniteDimensional ℂ M]

theorem GroundTheory.Automorphic.RestrictedTensor.exists_rankOne (T : Set (End ℂ M)) [Nontrivial M] :
    ∃ N : Submodule ℂ M, N ≠ ⊥ ∧ IsStable T N ∧ ∃ p ∈ Algebra.adjoin ℂ T, ∃ n₀ ∈ N, n₀ ≠ 0 ∧
      p n₀ = n₀ ∧ ∀ x ∈ N, ∃ c : ℂ, p x = c • n₀ := by sorry
