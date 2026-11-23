-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_isDomain_atPrime
-- name    : GlobalTheory.PrimeElement.isDomain_atPrime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:50.123532+00:00
-- url     : https://prove2.me/theorems/e73eb09a-0efe-4986-8b50-3d8e0d91cbf7
-- title:
--   Prime Element: is Domain at Prime
-- statement:
--   The Prime Element construction uses the is Domain at Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L40-L41

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
include π

theorem GlobalTheory.PrimeElement.isDomain_atPrime [IsDomain R] : IsDomain S := by sorry
