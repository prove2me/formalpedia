-- Prove2me | Theorems.Thm_GlobalTheory_T_inv_five_log_le_sum_inv_primes_half_interval
-- name    : GlobalTheory.T.inv_five_log_le_sum_inv_primes_half_interval
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:52:01.418249+00:00
-- url     : https://prove2.me/theorems/571dac31-5b9b-4a72-9668-b4b0e06676ac
-- title:
--   T: inv five log le sum inv primes half interval
-- statement:
--   The T construction uses the inv five log le sum inv primes half interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.inv_five_log_le_sum_inv_primes_half_interval : ∀ N : ℕ, 100 ≤ N → 1 / (5 * Real.log N) ≤ ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N), (1 : ℝ) / p := by sorry
