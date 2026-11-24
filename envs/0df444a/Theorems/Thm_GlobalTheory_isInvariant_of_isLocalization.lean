-- Prove2me | Theorems.Thm_GlobalTheory_isInvariant_of_isLocalization
-- name    : GlobalTheory.isInvariant_of_isLocalization
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:28.315142+00:00
-- url     : https://prove2.me/theorems/32eab540-11af-49af-897b-468f9767ffe8
-- title:
--   Global Theory: is Invariant of is Localization
-- statement:
--   The Global Theory construction uses the is Invariant of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L450-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L450-L473

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
variable (G : Type*) [Group G]
variable {A : Type*} [CommRing A] [MulSemiringAction G A]
variable {B : Type*} [CommRing B] [Algebra B A] [SMulCommClass G B A]

theorem GlobalTheory.isInvariant_of_isLocalization [Finite G] [Algebra.IsInvariant B A G]
    (T : Submonoid B) (B' A' : Type*) [CommRing B'] [CommRing A'] [Algebra B B'] [Algebra A A']
    [Algebra B' A'] [Algebra B A'] [IsScalarTower B B' A'] [IsScalarTower B A A']
    [IsLocalization T B'] [IsLocalization (Algebra.algebraMapSubmonoid A T) A']
    [MulSemiringAction G A'] [SMulDistribClass G A A'] :
    SMulCommClass G B' A' ∧ Algebra.IsInvariant B' A' G ∧
      (FaithfulSMul B A → FaithfulSMul B' A') := by sorry
