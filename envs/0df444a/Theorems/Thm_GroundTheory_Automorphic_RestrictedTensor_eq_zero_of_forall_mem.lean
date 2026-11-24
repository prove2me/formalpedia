-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_mem
-- name    : GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_forall_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:32:49.823386+00:00
-- url     : https://prove2.me/theorems/9389918f-3db0-4af4-8efb-89b037f0813d
-- title:
--   Restricted Tensor: eq zero of forall mem
-- statement:
--   The Restricted Tensor construction uses the eq zero of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L123-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L123-L161

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
omit [FiniteDimensional ℂ M]

theorem GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_forall_mem {T₁ T₂ : Set (End ℂ M)} (h : IsSimpleUnder (T₁ ∪ T₂))
    (hc : ∀ a ∈ T₁, ∀ b ∈ T₂, Commute a b) {N : Submodule ℂ M} (hN : N ≠ ⊥) (hNs : IsStable T₁ N)
    {a : End ℂ M} (ha : ∀ b ∈ T₂, Commute a b) (h0 : ∀ x ∈ N, a x = 0) : a = 0 := by sorry
