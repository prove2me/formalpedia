-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_isLyndon_append
-- name    : GlobalTheory.Lyndon.isLyndon_append
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:40.092267+00:00
-- url     : https://prove2.me/theorems/dd94cff8-3ae6-460a-bc35-21e2a174c68b
-- title:
--   Lyndon: is Lyndon append
-- statement:
--   The Lyndon construction uses the is Lyndon append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L226-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L226-L242

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

theorem GlobalTheory.Lyndon.isLyndon_append {l m : List A} (hl : IsLyndon l) (hm : IsLyndon m) (h : l < m) :
    IsLyndon (l ++ m) := by sorry
