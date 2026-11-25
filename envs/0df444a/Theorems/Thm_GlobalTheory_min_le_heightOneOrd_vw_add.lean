-- Prove2me | Theorems.Thm_GlobalTheory_min_le_heightOneOrd_vw_add
-- name    : GlobalTheory.min_le_heightOneOrd_vw_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:11.126526+00:00
-- url     : https://prove2.me/theorems/8040b8b2-f7d7-474d-80fa-4b363d33c7b0
-- title:
--   Global Theory: min le height One Ord vw add
-- statement:
--   The Global Theory construction uses the min le height One Ord vw add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L568-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L568-L575

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
variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)

theorem GlobalTheory.min_le_heightOneOrd_vw_add {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (heightOneOrd_vw p hp x) (heightOneOrd_vw p hp y) ≤ heightOneOrd_vw p hp (x + y) := by sorry
