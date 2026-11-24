-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_exists_unit_algebraMap_eq_of_valuation_eq_one
-- name    : GlobalTheory.PrimeElement.exists_unit_algebraMap_eq_of_valuation_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:27.718947+00:00
-- url     : https://prove2.me/theorems/5f176d63-4bfc-4989-8876-7c1499632a80
-- title:
--   Prime Element: exists unit algebra Map eq of valuation eq one
-- statement:
--   The Prime Element construction uses the exists unit algebra Map eq of valuation eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L148-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L148-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}
variable [(Ideal.span {π}).IsPrime]
  {A : Type*} [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  [IsDomain S] [IsDiscreteValuationRing S]
  (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K] [IsFractionRing S K]

theorem GlobalTheory.PrimeElement.exists_unit_algebraMap_eq_of_valuation_eq_one (hπ : π ≠ 0) {y : A} (hy : IsUnit y)
    (h : (IsDiscreteValuationRing.maximalIdeal S).valuation K (algebraMap A K y) = 1) :
    ∃ r : R, IsUnit r ∧ algebraMap R A r = y := by sorry
