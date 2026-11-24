-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_of_mem_adjoin
-- name    : GroundTheory.Automorphic.RestrictedTensor.commute_of_mem_adjoin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:41.916012+00:00
-- url     : https://prove2.me/theorems/ec41b137-d6ae-4e86-9886-b2855c6391be
-- title:
--   Restricted Tensor: commute of mem adjoin
-- statement:
--   The Restricted Tensor construction uses the commute of mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L37-L44

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

theorem GroundTheory.Automorphic.RestrictedTensor.commute_of_mem_adjoin {T : Set (End ℂ M)} {a : End ℂ M} (ha : ∀ t ∈ T, Commute a t) :
    ∀ b ∈ Algebra.adjoin ℂ T, Commute a b := by sorry
