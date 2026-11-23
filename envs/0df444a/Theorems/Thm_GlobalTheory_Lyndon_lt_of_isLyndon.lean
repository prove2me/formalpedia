-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_lt_of_isLyndon
-- name    : GlobalTheory.Lyndon.lt_of_isLyndon
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:31.029594+00:00
-- url     : https://prove2.me/theorems/b3695f12-e2dc-45a4-8f4e-c671c9cb99c4
-- title:
--   Lyndon: lt of is Lyndon
-- statement:
--   The Lyndon construction uses the lt of is Lyndon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L187-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L187-L188

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

theorem GlobalTheory.Lyndon.lt_of_isLyndon {w : List A} (h : IsLyndon w) {u v : List A} (hu : u ≠ []) (hv : v ≠ [])
    (e : w = u ++ v) : w < v := by sorry
