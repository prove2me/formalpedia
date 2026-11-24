-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_interleaves_split
-- name    : GlobalTheory.Lyndon.interleaves_split
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:34.356745+00:00
-- url     : https://prove2.me/theorems/a34adb5e-d28b-46df-a1ab-2c3ad62f86ab
-- title:
--   Lyndon: interleaves split
-- statement:
--   The Lyndon construction uses the interleaves split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L365-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L365-L385

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

theorem GlobalTheory.Lyndon.interleaves_split (w : List A) : ∀ (x y : List A) (S : Multiset (List A)),
    Interleaves w ((x ++ y) ::ₘ S) → Interleaves w (x ::ₘ y ::ₘ S) := by sorry
