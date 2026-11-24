-- Prove2me | Theorems.Thm_GlobalTheory_height_eq_one_of_mem_associatedPrimes
-- name    : GlobalTheory.height_eq_one_of_mem_associatedPrimes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:20.186907+00:00
-- url     : https://prove2.me/theorems/12b33929-a104-4422-a457-5ec822b183c8
-- title:
--   Global Theory: height eq one of mem associated Primes
-- statement:
--   The Global Theory construction uses the height eq one of mem associated Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L89-L96

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

theorem GlobalTheory.height_eq_one_of_mem_associatedPrimes {a : A} (ha : a ≠ 0) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {a})) : p.height = 1 := by sorry
