-- Prove2me | Theorems.Thm_GlobalTheory_CokerMinimalPrimes_exists_nat_mem_sup
-- name    : GlobalTheory.CokerMinimalPrimes.exists_nat_mem_sup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:15:03.605505+00:00
-- url     : https://prove2.me/theorems/5a5e5639-fab2-4495-bc82-1f60bf954439
-- title:
--   Coker Minimal Primes: exists nat mem sup
-- statement:
--   The Coker Minimal Primes construction uses the exists nat mem sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNatMulMemRangePiQuotientMinimalPrimes.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNatMulMemRangePiQuotientMinimalPrimes.lean#L5-L25

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

theorem GlobalTheory.CokerMinimalPrimes.exists_nat_mem_sup (B : Type) [CommRing B] [Module.Finite ℤ B]
    {P Q : Ideal B} (hP : P ∈ minimalPrimes B) (hQ : Q ∈ minimalPrimes B) (hPQ : P ≠ Q) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : B) ∈ P ⊔ Q := by sorry
