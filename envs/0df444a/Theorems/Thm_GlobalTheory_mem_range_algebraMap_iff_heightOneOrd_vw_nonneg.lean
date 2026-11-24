-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_algebraMap_iff_heightOneOrd_vw_nonneg
-- name    : GlobalTheory.mem_range_algebraMap_iff_heightOneOrd_vw_nonneg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:08.602414+00:00
-- url     : https://prove2.me/theorems/12778c00-5bc6-43af-8369-273401696873
-- title:
--   Global Theory: mem range algebra Map iff height One Ord vw nonneg
-- statement:
--   The Global Theory construction uses the mem range algebra Map iff height One Ord vw nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L579-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L579-L584

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

theorem GlobalTheory.mem_range_algebraMap_iff_heightOneOrd_vw_nonneg {x : K} (hx : x ≠ 0) :
    x ∈ (algebraMap A K).range ↔
      ∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1), 0 ≤ heightOneOrd_vw p hp x := by sorry
