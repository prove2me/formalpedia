-- Prove2me | Theorems.Thm_GlobalTheory_exists_unit_smul_eq_iff_heightOneOrd_vw_eq
-- name    : GlobalTheory.exists_unit_smul_eq_iff_heightOneOrd_vw_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:36.296826+00:00
-- url     : https://prove2.me/theorems/f9b6ebf4-4c7d-4697-aac3-7a821648eab9
-- title:
--   Global Theory: exists unit smul eq iff height One Ord vw eq
-- statement:
--   The Global Theory construction uses the exists unit smul eq iff height One Ord vw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L594-L612
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L594-L612

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

theorem GlobalTheory.exists_unit_smul_eq_iff_heightOneOrd_vw_eq {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ u : Aˣ, u • y = x) ↔ ∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
      heightOneOrd_vw p hp x = heightOneOrd_vw p hp y := by sorry
