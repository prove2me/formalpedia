-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_primes_dvd_of_dvd_mul_localization
-- name    : GlobalTheory.exists_finite_primes_dvd_of_dvd_mul_localization
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:46.023047+00:00
-- url     : https://prove2.me/theorems/50b673a4-9bb2-5bbe-9f17-f65b3c1e7498
-- title:
--   Global Theory: exists finite primes dvd of dvd mul localization
-- statement:
--   The Global Theory construction uses the exists finite primes dvd of dvd mul localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePrimesDvdOfDvdMulLocalization.lean#L22-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePrimesDvdOfDvdMulLocalization.lean#L22-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePrimesDvdOfDvdMulLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_finite_primes_dvd_of_dvd_mul_localization :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (s : R), s ≠ 0 → ∃ S : Set (PrimeSpectrum R), S.Finite ∧ ∀ (P : PrimeSpectrum R) (τ g : Localization.AtPrime P.asIdeal), (∀ Q ∈ S, Q ≤ P → τ ∉ Q.asIdeal.map (algebraMap R (Localization.AtPrime P.asIdeal))) → algebraMap R _ s ∣ g * τ → algebraMap R _ s ∣ g := by sorry
