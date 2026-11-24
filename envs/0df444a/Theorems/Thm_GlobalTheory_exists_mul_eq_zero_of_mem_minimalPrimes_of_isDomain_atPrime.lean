-- Prove2me | Theorems.Thm_GlobalTheory_exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime
-- name    : GlobalTheory.exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:35:11.228616+00:00
-- url     : https://prove2.me/theorems/eb713ac2-65a3-42f0-9f7c-36dbad2fa6f8
-- title:
--   Global Theory: exists mul eq zero of mem minimal Primes of is Domain at Prime
-- statement:
--   The Global Theory construction uses the exists mul eq zero of mem minimal Primes of is Domain at Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsIntegrallyClosedQuotientOfMemMinimalPrimes.lean#L6-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsIntegrallyClosedQuotientOfMemMinimalPrimes.lean#L6-L22

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

theorem GlobalTheory.exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime {S : Type*} [CommRing S]
    {q : Ideal S} (hq : q ∈ minimalPrimes S) (m : Ideal S) [m.IsPrime] (hqm : q ≤ m)
    [IsDomain (Localization.AtPrime m)] {x : S} (hx : x ∈ q) :
    ∃ s : m.primeCompl, (s : S) * x = 0 := by sorry
