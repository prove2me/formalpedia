-- Prove2me | Theorems.Thm_GlobalTheory_heightOneOrd_vw_div
-- name    : GlobalTheory.heightOneOrd_vw_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:19.039867+00:00
-- url     : https://prove2.me/theorems/443a2a2b-0041-4a51-bbcb-5fc73acde0a5
-- title:
--   Global Theory: height One Ord vw div
-- statement:
--   The Global Theory construction uses the height One Ord vw div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L425-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L425-L428

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
variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)

theorem GlobalTheory.heightOneOrd_vw_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    heightOneOrd_vw p hp (x / y) = heightOneOrd_vw p hp x - heightOneOrd_vw p hp y := by sorry
