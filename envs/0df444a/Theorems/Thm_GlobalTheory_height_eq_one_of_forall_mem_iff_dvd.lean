-- Prove2me | Theorems.Thm_GlobalTheory_height_eq_one_of_forall_mem_iff_dvd
-- name    : GlobalTheory.height_eq_one_of_forall_mem_iff_dvd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:38.938365+00:00
-- url     : https://prove2.me/theorems/e17ed827-c83d-4f51-a90b-26b172258ab3
-- title:
--   Global Theory: height eq one of forall mem iff dvd
-- statement:
--   The Global Theory construction uses the height eq one of forall mem iff dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L54-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L54-L87

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
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
variable [IsIntegrallyClosed A]

theorem GlobalTheory.height_eq_one_of_forall_mem_iff_dvd {p : Ideal A} [hp : p.IsPrime] {a b : A} (ha : a ≠ 0)
    (h : ∀ r, r ∈ p ↔ a ∣ r * b) : p.height = 1 := by sorry
