-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_algebraMap_of_pow_smul_mem
-- name    : GlobalTheory.mem_range_algebraMap_of_pow_smul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:21.897116+00:00
-- url     : https://prove2.me/theorems/7640a302-64be-5002-b594-dcb1251ac689
-- title:
--   Global Theory: mem range algebra Map of pow smul mem
-- statement:
--   The Global Theory construction uses the mem range algebra Map of pow smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L479-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L479-L484

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

theorem GlobalTheory.mem_range_algebraMap_of_pow_smul_mem {x : K} {a : A} (ha : a ≠ 0) {n : ℕ}
    (hax : a ^ n • x ∈ (algebraMap A K).range)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p → x ∈ primeLocalSubalgebra K p) :
    x ∈ (algebraMap A K).range := by sorry
