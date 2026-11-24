-- Prove2me | Theorems.Thm_GlobalTheory_NatCastMemOfPrimeDvdNorm_natCast_mem_of_prime_dvd_absNorm
-- name    : GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:23:16.025391+00:00
-- url     : https://prove2.me/theorems/c5f67569-fb5f-42a6-9931-a5d7671a8374
-- title:
--   Nat Cast Mem Of Prime Dvd Norm: nat Cast mem of prime dvd abs Norm
-- statement:
--   The Nat Cast Mem Of Prime Dvd Norm construction uses the nat Cast mem of prime dvd abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NatCastMemOfPrimeDvdAbsNorm.lean#L7-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NatCastMemOfPrimeDvdAbsNorm.lean#L7-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NatCastMemOfPrimeDvdAbsNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatCastMemOfPrimeDvdNorm
open NumberField IsDedekindDomain

theorem GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (RingOfIntegers K)) {q : ℕ} (hq : Nat.Prime q)
    (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : RingOfIntegers K) ∈ w.asIdeal := by sorry
