-- Prove2me | Theorems.Thm_GlobalTheory_PrimeRecip_okIv_sound
-- name    : GlobalTheory.PrimeRecip.okIv_sound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:50:48.477007+00:00
-- url     : https://prove2.me/theorems/8e377248-b391-4cac-8df0-0bdf6abae6bb
-- title:
--   Prime Recip: ok Iv sound
-- statement:
--   The Prime Recip construction uses the ok Iv sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L60-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L60-L107

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

theorem GlobalTheory.PrimeRecip.okIv_sound {a b j c : ℕ} {L : List ℕ} (h : okIv a b j c L = true) (N : ℕ) (haN : a ≤ N)
    (hNb : N < b) :
    1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by sorry
