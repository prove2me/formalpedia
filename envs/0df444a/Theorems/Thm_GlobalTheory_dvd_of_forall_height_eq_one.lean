-- Prove2me | Theorems.Thm_GlobalTheory_dvd_of_forall_height_eq_one
-- name    : GlobalTheory.dvd_of_forall_height_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:01.671705+00:00
-- url     : https://prove2.me/theorems/d2b09fe7-ae37-4a68-81b0-6b1663292610
-- title:
--   Global Theory: dvd of forall height eq one
-- statement:
--   The Global Theory construction uses the dvd of forall height eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L113-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L113-L124

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

theorem GlobalTheory.dvd_of_forall_height_eq_one {a b : A} (ha : a ≠ 0)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p → ∃ s, s ∉ p ∧ a ∣ s * b) : a ∣ b := by sorry
