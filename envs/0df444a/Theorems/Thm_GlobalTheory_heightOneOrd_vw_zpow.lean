-- Prove2me | Theorems.Thm_GlobalTheory_heightOneOrd_vw_zpow
-- name    : GlobalTheory.heightOneOrd_vw_zpow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:42.33945+00:00
-- url     : https://prove2.me/theorems/d046dd7d-6fb8-49d6-a71e-c5b48284a678
-- title:
--   Global Theory: height One Ord vw zpow
-- statement:
--   The Global Theory construction uses the height One Ord vw zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L430-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L430-L433

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

theorem GlobalTheory.heightOneOrd_vw_zpow (x : K) (n : ℤ) :
    heightOneOrd_vw p hp (x ^ n) = n * heightOneOrd_vw p hp x := by sorry
