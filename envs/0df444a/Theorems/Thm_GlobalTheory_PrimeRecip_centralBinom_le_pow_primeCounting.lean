-- Prove2me | Theorems.Thm_GlobalTheory_PrimeRecip_centralBinom_le_pow_primeCounting
-- name    : GlobalTheory.PrimeRecip.centralBinom_le_pow_primeCounting
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:50:02.94008+00:00
-- url     : https://prove2.me/theorems/1d00ed3f-39ea-5633-99b4-87b02d0c4285
-- title:
--   Prime Recip: central Binom le pow prime Counting
-- statement:
--   The Prime Recip construction uses the central Binom le pow prime Counting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L129-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L129-L184

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

theorem GlobalTheory.PrimeRecip.centralBinom_le_pow_primeCounting (n : ℕ) (n_large : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.primeCounting (Nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) *
      (2 * n) ^ ((Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)).card := by sorry
