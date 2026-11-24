-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_le_flatten_of_interleaves
-- name    : GlobalTheory.Lyndon.le_flatten_of_interleaves
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:46.062846+00:00
-- url     : https://prove2.me/theorems/c9d9051b-5591-45ed-9d1e-ab10456ea84a
-- title:
--   Lyndon: le flatten of interleaves
-- statement:
--   The Lyndon construction uses the le flatten of interleaves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L493-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L493-L506

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

theorem GlobalTheory.Lyndon.le_flatten_of_interleaves (w : List A) : ∀ L : List (List A), IsFactors L →
    Interleaves w ↑L → w ≤ L.flatten := by sorry
