-- Prove2me | Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_height_eq_one
-- name    : GlobalTheory.mem_associatedPrimes_iff_height_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:48.100824+00:00
-- url     : https://prove2.me/theorems/e4d54462-0ac6-4259-a2db-9f360dde9b49
-- title:
--   Global Theory: mem associated Primes iff height eq one
-- statement:
--   The Global Theory construction uses the mem associated Primes iff height eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L98-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L98-L111

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

theorem GlobalTheory.mem_associatedPrimes_iff_height_eq_one {a : A} (ha : a ≠ 0) {p : Ideal A} :
    p ∈ associatedPrimes A (A ⧸ Ideal.span {a}) ↔ p.IsPrime ∧ p.height = 1 ∧ a ∈ p := by sorry
