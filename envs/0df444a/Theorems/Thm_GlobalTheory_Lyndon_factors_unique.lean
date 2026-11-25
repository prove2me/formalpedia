-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_factors_unique
-- name    : GlobalTheory.Lyndon.factors_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:39.756426+00:00
-- url     : https://prove2.me/theorems/788fbc8c-915e-4b12-a125-19ddaf5376a6
-- title:
--   Lyndon: factors unique
-- statement:
--   The Lyndon construction uses the factors unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L301-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L301-L322

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

theorem GlobalTheory.Lyndon.factors_unique (L : List (List A)) (hL : IsFactors L) :
    ∀ L', IsFactors L' → L.flatten = L'.flatten → L = L' := by sorry
