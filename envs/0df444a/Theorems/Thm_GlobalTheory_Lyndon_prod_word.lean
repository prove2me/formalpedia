-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_prod_word
-- name    : GlobalTheory.Lyndon.prod_word
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:56.437506+00:00
-- url     : https://prove2.me/theorems/0a4d3ccb-09f3-4fa1-86ef-b4a677d3ff62
-- title:
--   Lyndon: prod word
-- statement:
--   The Lyndon construction uses the prod word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L534-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L534-L541

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
open ShuffleAlgebra
variable (K : Type) [Field K]
omit [LinearOrder A]

theorem GlobalTheory.Lyndon.prod_word (L : List (List A)) :
    (L.map (word K)).prod = ((shuffleList L).map (word K)).sum := by sorry
