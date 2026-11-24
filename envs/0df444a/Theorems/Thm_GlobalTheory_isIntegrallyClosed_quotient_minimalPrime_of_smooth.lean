-- Prove2me | Theorems.Thm_GlobalTheory_isIntegrallyClosed_quotient_minimalPrime_of_smooth
-- name    : GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:56:49.695589+00:00
-- url     : https://prove2.me/theorems/d9dd808b-72c3-4c2c-971e-a1fa3526e988
-- title:
--   Global Theory: is Integrally Closed quotient minimal Prime of smooth
-- statement:
--   The Global Theory construction uses the is Integrally Closed quotient minimal Prime of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsIntegrallyClosedQuotientOfMemMinimalPrimes.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsIntegrallyClosedQuotientOfMemMinimalPrimes.lean#L72-L77

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

theorem GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth :
    ∀ (F S : Type) [Field F] [CommRing S] [Algebra F S] [Algebra.Smooth F S] (q : Ideal S),
      q ∈ minimalPrimes S → IsIntegrallyClosed (S ⧸ q) := by sorry
