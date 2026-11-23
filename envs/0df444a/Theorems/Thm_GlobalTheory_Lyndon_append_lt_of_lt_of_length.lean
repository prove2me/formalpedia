-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_append_lt_of_lt_of_length
-- name    : GlobalTheory.Lyndon.append_lt_of_lt_of_length
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:51.063872+00:00
-- url     : https://prove2.me/theorems/ad4de796-bb6f-40a1-ba93-e7bf83d3505f
-- title:
--   Lyndon: append lt of lt of length
-- statement:
--   The Lyndon construction uses the append lt of lt of length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L202-L206

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

theorem GlobalTheory.Lyndon.append_lt_of_lt_of_length {u v : List A} (h : u < v) (hl : v.length ≤ u.length)
    (x y : List A) : u ++ x < v ++ y := by sorry
