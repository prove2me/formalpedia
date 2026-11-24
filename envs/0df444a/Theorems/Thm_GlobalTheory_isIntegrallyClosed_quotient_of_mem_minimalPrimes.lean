-- Prove2me | Theorems.Thm_GlobalTheory_isIntegrallyClosed_quotient_of_mem_minimalPrimes
-- name    : GlobalTheory.isIntegrallyClosed_quotient_of_mem_minimalPrimes
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:56:47.815845+00:00
-- url     : https://prove2.me/theorems/edf31ef2-8f3b-4734-a9d1-ca97cbb995dc
-- title:
--   Global Theory: is Integrally Closed quotient of mem minimal Primes
-- statement:
--   The Global Theory construction uses the is Integrally Closed quotient of mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsIntegrallyClosedQuotientOfMemMinimalPrimes.lean#L24-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsIntegrallyClosedQuotientOfMemMinimalPrimes.lean#L24-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.isIntegrallyClosed_quotient_of_mem_minimalPrimes {S : Type*} [CommRing S]
    (hS : ∀ (m : Ideal S) [m.IsPrime],
      IsDomain (Localization.AtPrime m) ∧ IsIntegrallyClosed (Localization.AtPrime m))
    {q : Ideal S} (hq : q ∈ minimalPrimes S) : IsIntegrallyClosed (S ⧸ q) := by sorry
