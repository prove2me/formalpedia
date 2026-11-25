-- Prove2me | Theorems.Thm_GlobalTheory_PrimeRecip_prime_of_check
-- name    : GlobalTheory.PrimeRecip.prime_of_check
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:50:19.055796+00:00
-- url     : https://prove2.me/theorems/a81a5b40-5a1d-5142-8693-686a25d3a8ca
-- title:
--   Prime Recip: prime of check
-- statement:
--   The Prime Recip construction uses the prime of check property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L41-L47

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

theorem GlobalTheory.PrimeRecip.prime_of_check {p : ℕ} (h2 : 2 ≤ p) (hp : p < 17161) (h : noSmallDiv p 130 = true) :
    p.Prime := by sorry
