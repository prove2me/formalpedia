-- Prove2me | Theorems.Thm_GlobalTheory_exists_orbit_eq_primesOver_of_isInvariant
-- name    : GlobalTheory.exists_orbit_eq_primesOver_of_isInvariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:23:57.89215+00:00
-- url     : https://prove2.me/theorems/c8d5c152-f943-4f69-9ecf-dbccc752a438
-- title:
--   Global Theory: exists orbit eq primes Over of is Invariant
-- statement:
--   The Global Theory construction uses the exists orbit eq primes Over of is Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L109-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]

theorem GlobalTheory.exists_orbit_eq_primesOver_of_isInvariant [Finite G] (B : Type*) [CommRing B]
    [Algebra B A] [FaithfulSMul B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    (P : Ideal B) [P.IsPrime] :
    ∃ Q : Ideal A, Q.IsPrime ∧ Q.LiesOver P ∧ MulAction.orbit G Q = P.primesOver A := by sorry
