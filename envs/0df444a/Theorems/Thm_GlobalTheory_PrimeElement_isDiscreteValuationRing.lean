-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_isDiscreteValuationRing
-- name    : GlobalTheory.PrimeElement.isDiscreteValuationRing
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:31.717804+00:00
-- url     : https://prove2.me/theorems/c304bb76-b1af-4ce7-ae21-1a79d4c5f3d4
-- title:
--   Prime Element: is Discrete Valuation Ring
-- statement:
--   The Prime Element construction uses the is Discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L43-L54

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
variable [(Ideal.span {π}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S (Ideal.span {π})]

theorem GlobalTheory.PrimeElement.isDiscreteValuationRing [IsDomain R] [IsNoetherianRing R] [IsDomain S] (hπ : π ≠ 0) :
    IsDiscreteValuationRing S := by sorry
