-- Prove2me | Theorems.Thm_GlobalTheory_prime_algebraMap_localization_of_isRegularRing_quotient
-- name    : GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:15:37.447609+00:00
-- url     : https://prove2.me/theorems/0b44db28-0c0d-4eb7-a253-acd2ce23f887
-- title:
--   Global Theory: prime algebra Map localization of is Regular Ring quotient
-- statement:
--   The Global Theory construction uses the prime algebra Map localization of is Regular Ring quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RegularQuotientPrimeElement.lean#L6-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RegularQuotientPrimeElement.lean#L6-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RegularQuotientPrimeElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient :
    ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P →
      IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by sorry
