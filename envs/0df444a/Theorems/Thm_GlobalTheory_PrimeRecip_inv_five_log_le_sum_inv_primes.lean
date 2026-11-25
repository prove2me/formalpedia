-- Prove2me | Theorems.Thm_GlobalTheory_PrimeRecip_inv_five_log_le_sum_inv_primes
-- name    : GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:50:38.240805+00:00
-- url     : https://prove2.me/theorems/6f1c8d5a-529c-4334-8587-337a3dadd9d8
-- title:
--   Prime Recip: inv five log le sum inv primes
-- statement:
--   The Prime Recip construction uses the inv five log le sum inv primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L303-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L303-L310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open GlobalTheory GlobalTheory.PrimeRecip

theorem GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes :
    ∀ N : ℕ, 100 ≤ N → 1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by sorry
