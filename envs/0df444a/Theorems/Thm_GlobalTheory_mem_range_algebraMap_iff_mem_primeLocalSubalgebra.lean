-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_algebraMap_iff_mem_primeLocalSubalgebra
-- name    : GlobalTheory.mem_range_algebraMap_iff_mem_primeLocalSubalgebra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:26.056717+00:00
-- url     : https://prove2.me/theorems/06a97e11-203a-4e2a-ae19-44c1c0814d68
-- title:
--   Global Theory: mem range algebra Map iff mem prime Local Subalgebra
-- statement:
--   The Global Theory construction uses the mem range algebra Map iff mem prime Local Subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L349-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L349-L353

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

theorem GlobalTheory.mem_range_algebraMap_iff_mem_primeLocalSubalgebra (p : Ideal A) [p.IsPrime]
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.AtPrime B p] [Algebra B K]
    [IsScalarTower A B K] (x : K) :
    x ∈ (algebraMap B K).range ↔ x ∈ primeLocalSubalgebra K p := by sorry
