-- Prove2me | Theorems.Thm_GlobalTheory_CokerMinimalPrimes_exists_nat_mul_mem_range_pi_quotient_minimalPrimes
-- name    : GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:15:10.137912+00:00
-- url     : https://prove2.me/theorems/b4c15f87-928b-494f-8fca-538f846d9407
-- title:
--   Coker Minimal Primes: exists nat mul mem range pi quotient minimal Primes
-- statement:
--   The Coker Minimal Primes construction uses the exists nat mul mem range pi quotient minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNatMulMemRangePiQuotientMinimalPrimes.lean#L64-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNatMulMemRangePiQuotientMinimalPrimes.lean#L64-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNatMulMemRangePiQuotientMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CokerMinimalPrimes

theorem GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧
    ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)),
      (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈
        (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by sorry
