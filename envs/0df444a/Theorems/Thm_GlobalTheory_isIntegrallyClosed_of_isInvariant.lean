-- Prove2me | Theorems.Thm_GlobalTheory_isIntegrallyClosed_of_isInvariant
-- name    : GlobalTheory.isIntegrallyClosed_of_isInvariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:59.638199+00:00
-- url     : https://prove2.me/theorems/71318486-77a3-4e98-a785-52c4d9ebb550
-- title:
--   Global Theory: is Integrally Closed of is Invariant
-- statement:
--   The Global Theory construction uses the is Integrally Closed of is Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L32-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L32-L67

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

theorem GlobalTheory.isIntegrallyClosed_of_isInvariant (B : Type*) [CommRing B] [Algebra B A]
    [FaithfulSMul B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    [IsDomain A] [IsIntegrallyClosed A] : IsDomain B ∧ IsIntegrallyClosed B := by sorry
