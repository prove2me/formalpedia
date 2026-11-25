-- Prove2me | Theorems.Thm_GlobalTheory_PrimeRecip_noSmallDiv_spec
-- name    : GlobalTheory.PrimeRecip.noSmallDiv_spec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:50:15.371027+00:00
-- url     : https://prove2.me/theorems/519e4b59-7d65-4d70-9df1-8a719dfa2f3c
-- title:
--   Prime Recip: no Small Div spec
-- statement:
--   The Prime Recip construction uses the no Small Div spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L22-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L22-L39

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

theorem GlobalTheory.PrimeRecip.noSmallDiv_spec (p : ℕ) : ∀ D, noSmallDiv p D = true →
    ∀ d, 2 ≤ d → d ≤ D → d * d ≤ p → p % d ≠ 0 := by sorry
