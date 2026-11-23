-- Prove2me | Theorems.Thm_GlobalTheory_mem_minimalPrimes_span_singleton_of_height_eq_one
-- name    : GlobalTheory.mem_minimalPrimes_span_singleton_of_height_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:12.598215+00:00
-- url     : https://prove2.me/theorems/68725561-117f-448d-9a02-dfdbe65ab5db
-- title:
--   Global Theory: mem minimal Primes span singleton of height eq one
-- statement:
--   The Global Theory construction uses the mem minimal Primes span singleton of height eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L11-L21

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

theorem GlobalTheory.mem_minimalPrimes_span_singleton_of_height_eq_one {p : Ideal A} [p.IsPrime]
    (hp : p.height = 1) {a : A} (ha : a ≠ 0) (hap : a ∈ p) :
    p ∈ (Ideal.span {a}).minimalPrimes := by sorry
