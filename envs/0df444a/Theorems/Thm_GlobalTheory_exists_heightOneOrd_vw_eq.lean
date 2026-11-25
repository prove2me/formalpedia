-- Prove2me | Theorems.Thm_GlobalTheory_exists_heightOneOrd_vw_eq
-- name    : GlobalTheory.exists_heightOneOrd_vw_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:08.690507+00:00
-- url     : https://prove2.me/theorems/1ed24191-8bda-474c-a646-30f24e817b7d
-- title:
--   Global Theory: exists height One Ord vw eq
-- statement:
--   The Global Theory construction uses the exists height One Ord vw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L536-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L536-L540

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

theorem GlobalTheory.exists_heightOneOrd_vw_eq (n : ℤ) : ∃ x : K, x ≠ 0 ∧ heightOneOrd_vw p hp x = n := by sorry
