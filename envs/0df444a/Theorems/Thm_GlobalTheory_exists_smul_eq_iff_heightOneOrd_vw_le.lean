-- Prove2me | Theorems.Thm_GlobalTheory_exists_smul_eq_iff_heightOneOrd_vw_le
-- name    : GlobalTheory.exists_smul_eq_iff_heightOneOrd_vw_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:18.000859+00:00
-- url     : https://prove2.me/theorems/384a05d7-9fa8-4dd5-889e-1259d03ef888
-- title:
--   Global Theory: exists smul eq iff height One Ord vw le
-- statement:
--   The Global Theory construction uses the exists smul eq iff height One Ord vw le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L586-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L586-L592

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

theorem GlobalTheory.exists_smul_eq_iff_heightOneOrd_vw_le {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ a : A, a • y = x) ↔ ∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
      heightOneOrd_vw p hp y ≤ heightOneOrd_vw p hp x := by sorry
