-- Prove2me | Theorems.Thm_GlobalTheory_ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime
-- name    : GlobalTheory.ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:52:48.982827+00:00
-- url     : https://prove2.me/theorems/aa634e69-b2f1-56c7-b0b9-6a5e007d6a71
-- title:
--   Global Theory: ring Krull Dim quotient eq trdeg of mem minimal Primes nat Prime
-- statement:
--   The Global Theory construction uses the ring Krull Dim quotient eq trdeg of mem minimal Primes nat Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullDimQuotientMinimalPrimeOverL.lean#L91-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullDimQuotientMinimalPrimeOverL.lean#L91-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimQuotientMinimalPrimeOverL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
universe u

theorem GlobalTheory.ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime (A : Type) [CommRing A]
    [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] (l : ℕ) [Fact l.Prime] (q : Ideal A)
    [q.IsPrime] (hq : q ∈ (Ideal.span {(l : A)}).minimalPrimes) (d : ℕ)
    (hd : Algebra.trdeg ℤ A = d) : ringKrullDim (A ⧸ q) = d := by sorry
