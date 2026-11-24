-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_interleaves_of_mem_shuffle
-- name    : GlobalTheory.Lyndon.interleaves_of_mem_shuffle
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:54.85373+00:00
-- url     : https://prove2.me/theorems/c58c5668-4cd9-429b-b897-eec9e8bf3728
-- title:
--   Lyndon: interleaves of mem shuffle
-- statement:
--   The Lyndon construction uses the interleaves of mem shuffle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L347-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L347-L362

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
omit [LinearOrder A]

theorem GlobalTheory.Lyndon.interleaves_of_mem_shuffle : ∀ (u x w : List A) (S : Multiset (List A)),
    w ∈ shuffle u x → Interleaves x S → Interleaves w (u ::ₘ S)
  := by sorry
