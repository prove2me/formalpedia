-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_algebraMap_iff_forall_height_eq_one
-- name    : GlobalTheory.mem_range_algebraMap_iff_forall_height_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:40.623396+00:00
-- url     : https://prove2.me/theorems/c400a050-f0df-43af-a703-4189a293ecf2
-- title:
--   Global Theory: mem range algebra Map iff forall height eq one
-- statement:
--   The Global Theory construction uses the mem range algebra Map iff forall height eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L486-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L486-L490

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

theorem GlobalTheory.mem_range_algebraMap_iff_forall_height_eq_one (x : K) :
    x ∈ (algebraMap A K).range ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → x ∈ primeLocalSubalgebra K p := by sorry
