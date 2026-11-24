-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_exists_unit_algebraMap_eq
-- name    : GlobalTheory.PrimeElement.exists_unit_algebraMap_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:17.389994+00:00
-- url     : https://prove2.me/theorems/99383563-65c8-4ba0-8c44-97d79e7a2ed4
-- title:
--   Prime Element: exists unit algebra Map eq
-- statement:
--   The Prime Element construction uses the exists unit algebra Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L124-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L124-L135

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
  (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  (K : Type*) [CommRing K] [IsDomain K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K]
variable {A S}

theorem GlobalTheory.PrimeElement.exists_unit_algebraMap_eq (hπ : π ≠ 0) {y : A} (hy : IsUnit y) {z : S} (hz : IsUnit z)
    (h : algebraMap A K y = algebraMap S K z) :
    ∃ r : R, IsUnit r ∧ algebraMap R A r = y := by sorry
