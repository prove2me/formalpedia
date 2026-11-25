-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_isUnit_algebraMap_iff
-- name    : GlobalTheory.PrimeElement.isUnit_algebraMap_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:02.207797+00:00
-- url     : https://prove2.me/theorems/654ea5cf-223a-4988-aaaf-4ba407229fc6
-- title:
--   Prime Element: is Unit algebra Map iff
-- statement:
--   The Prime Element construction uses the is Unit algebra Map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L32-L33

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

theorem GlobalTheory.PrimeElement.isUnit_algebraMap_iff (x : R) : IsUnit (algebraMap R S x) ↔ ¬ π ∣ x := by sorry
