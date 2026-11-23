-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_maximalIdeal_eq_span
-- name    : GlobalTheory.PrimeElement.maximalIdeal_eq_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:36.044239+00:00
-- url     : https://prove2.me/theorems/53f7b613-f03e-4c4b-9930-c286da7a0b8a
-- title:
--   Prime Element: maximal Ideal eq span
-- statement:
--   The Prime Element construction uses the maximal Ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L27-L30

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

theorem GlobalTheory.PrimeElement.maximalIdeal_eq_span [IsLocalRing S] :
    maximalIdeal S = Ideal.span {algebraMap R S π} := by sorry
