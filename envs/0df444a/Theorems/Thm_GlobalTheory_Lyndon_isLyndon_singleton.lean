-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_isLyndon_singleton
-- name    : GlobalTheory.Lyndon.isLyndon_singleton
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:57.656799+00:00
-- url     : https://prove2.me/theorems/571f94e9-afa2-4480-9c79-18544aa3fd3b
-- title:
--   Lyndon: is Lyndon singleton
-- statement:
--   The Lyndon construction uses the is Lyndon singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L223-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L223-L224

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

theorem GlobalTheory.Lyndon.isLyndon_singleton (a : A) : IsLyndon [a] := by sorry
