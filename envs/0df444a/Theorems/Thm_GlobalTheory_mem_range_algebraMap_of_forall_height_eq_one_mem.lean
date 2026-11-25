-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_algebraMap_of_forall_height_eq_one_mem
-- name    : GlobalTheory.mem_range_algebraMap_of_forall_height_eq_one_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:06.081317+00:00
-- url     : https://prove2.me/theorems/a3fc454c-9f1d-4bfa-bbad-314b0292b0f9
-- title:
--   Global Theory: mem range algebra Map of forall height eq one mem
-- statement:
--   The Global Theory construction uses the mem range algebra Map of forall height eq one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L471-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L471-L477

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

theorem GlobalTheory.mem_range_algebraMap_of_forall_height_eq_one_mem {x : K} {a : A} (ha : a ≠ 0)
    (hax : a • x ∈ (algebraMap A K).range)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p → x ∈ primeLocalSubalgebra K p) :
    x ∈ (algebraMap A K).range := by sorry
