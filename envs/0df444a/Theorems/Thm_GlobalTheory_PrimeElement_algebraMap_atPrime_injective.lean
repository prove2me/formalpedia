-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_algebraMap_atPrime_injective
-- name    : GlobalTheory.PrimeElement.algebraMap_atPrime_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:53:35.944806+00:00
-- url     : https://prove2.me/theorems/c3740b33-7478-4316-af7b-cfb908ea3516
-- title:
--   Prime Element: algebra Map at Prime injective
-- statement:
--   The Prime Element construction uses the algebra Map at Prime injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L36-L37

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

theorem GlobalTheory.PrimeElement.algebraMap_atPrime_injective [IsDomain R] : Function.Injective (algebraMap R S) := by sorry
