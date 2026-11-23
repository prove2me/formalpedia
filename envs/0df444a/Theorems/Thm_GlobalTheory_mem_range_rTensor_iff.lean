-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_rTensor_iff
-- name    : GlobalTheory.mem_range_rTensor_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:29.0475+00:00
-- url     : https://prove2.me/theorems/fb150b32-8703-4a35-bc5e-4f03c82a114f
-- title:
--   Global Theory: mem range r Tensor iff
-- statement:
--   The Global Theory construction uses the mem range r Tensor iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L305-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L305-L324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable (p : Ideal A) [p.IsPrime] (B : Type*) [CommRing B] [Algebra A B]
  [IsLocalization.AtPrime B p] [Algebra B K] [IsScalarTower A B K]

theorem GlobalTheory.mem_range_rTensor_iff {M : Type*} [AddCommGroup M] [Module A M] (v : K ⊗[A] M) :
    v ∈ LinearMap.range ((IsScalarTower.toAlgHom A B K).toLinearMap.rTensor M) ↔
      ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range (TensorProduct.mk A K M 1) := by sorry
