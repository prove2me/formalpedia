-- Prove2me | Theorems.Thm_GlobalTheory_PrimeRecip_okAll_sound
-- name    : GlobalTheory.PrimeRecip.okAll_sound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:50:44.57988+00:00
-- url     : https://prove2.me/theorems/900155b5-7ea5-4bce-8923-640cc956d50c
-- title:
--   Prime Recip: ok All sound
-- statement:
--   The Prime Recip construction uses the ok All sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L109-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L109-L119

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

theorem GlobalTheory.PrimeRecip.okAll_sound : ∀ (T : List (ℕ × ℕ × ℕ × ℕ × List ℕ)) (lo hi : ℕ), okAll lo T hi = true →
    ∀ N, lo ≤ N → N < hi → 1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p
  := by sorry
