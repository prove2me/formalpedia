-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_of_mem_adjoin_restrictSet
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_of_mem_adjoin_restrictSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:27.729775+00:00
-- url     : https://prove2.me/theorems/76655fac-9a99-41fa-ba95-5bb64ef153e2
-- title:
--   Restricted Tensor: exists of mem adjoin restrict Set
-- statement:
--   The Restricted Tensor construction uses the exists of mem adjoin restrict Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L168-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L168-L187

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

theorem GroundTheory.Automorphic.RestrictedTensor.exists_of_mem_adjoin_restrictSet {T : Set (End ℂ M)} {N : Submodule ℂ M}
    (hN : IsStable T N) {b : End ℂ N} (hb : b ∈ Algebra.adjoin ℂ (restrictSet T N hN)) :
    ∃ a ∈ Algebra.adjoin ℂ T, ∀ x : N, (b x : M) = a x := by sorry
