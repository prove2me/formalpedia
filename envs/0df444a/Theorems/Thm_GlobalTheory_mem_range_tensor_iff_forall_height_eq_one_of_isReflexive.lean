-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_tensor_iff_forall_height_eq_one_of_isReflexive
-- name    : GlobalTheory.mem_range_tensor_iff_forall_height_eq_one_of_isReflexive
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:00.170332+00:00
-- url     : https://prove2.me/theorems/1b94835a-8589-453b-b6a5-57238e5170e1
-- title:
--   Global Theory: mem range tensor iff forall height eq one of is Reflexive
-- statement:
--   The Global Theory construction uses the mem range tensor iff forall height eq one of is Reflexive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L509-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L509-L516

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
variable [IsNoetherianRing A]
variable [IsIntegrallyClosed A]

theorem GlobalTheory.mem_range_tensor_iff_forall_height_eq_one_of_isReflexive {M : Type*} [AddCommGroup M]
    [Module A M] [Module.IsReflexive A M] (v : K ⊗[A] M) :
    v ∈ LinearMap.range (TensorProduct.mk A K M 1) ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
        v ∈ LinearMap.range ((primeLocalSubalgebra K p).val.toLinearMap.rTensor M) := by sorry
