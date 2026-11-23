-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_append_lt_append_left
-- name    : GlobalTheory.Lyndon.append_lt_append_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:07.516874+00:00
-- url     : https://prove2.me/theorems/6f088545-0b3f-4077-aeed-a78ae5690daa
-- title:
--   Lyndon: append lt append left
-- statement:
--   The Lyndon construction uses the append lt append left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L208-L211

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

theorem GlobalTheory.Lyndon.append_lt_append_left (p : List A) {u v : List A} (h : u < v) : p ++ u < p ++ v := by sorry
