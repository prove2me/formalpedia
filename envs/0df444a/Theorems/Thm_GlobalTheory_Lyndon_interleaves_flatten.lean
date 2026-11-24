-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_interleaves_flatten
-- name    : GlobalTheory.Lyndon.interleaves_flatten
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:46.354983+00:00
-- url     : https://prove2.me/theorems/ae47d2df-8cf6-4eca-badb-836e214bbde6
-- title:
--   Lyndon: interleaves flatten
-- statement:
--   The Lyndon construction uses the interleaves flatten property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L388-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L388-L397

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

theorem GlobalTheory.Lyndon.interleaves_flatten (w : List A) (F : List (List A)) : ∀ S : Multiset (List A),
    Interleaves w (F.flatten ::ₘ S) → Interleaves w (↑F + S) := by sorry
