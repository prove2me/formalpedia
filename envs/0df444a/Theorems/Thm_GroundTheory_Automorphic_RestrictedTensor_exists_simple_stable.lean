-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_simple_stable
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_simple_stable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:37.041665+00:00
-- url     : https://prove2.me/theorems/4ee726fb-6177-41d1-a42e-3185aefdedad
-- title:
--   Restricted Tensor: exists simple stable
-- statement:
--   The Restricted Tensor construction uses the exists simple stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L189-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L189-L216

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

theorem GroundTheory.Automorphic.RestrictedTensor.exists_simple_stable (T : Set (End ℂ M)) [Nontrivial M] :
    ∃ (N : Submodule ℂ M) (hN : IsStable T N), N ≠ ⊥ ∧ IsSimpleUnder (restrictSet T N hN) := by sorry
