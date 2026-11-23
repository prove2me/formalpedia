-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_lt_cases
-- name    : GlobalTheory.Lyndon.lt_cases
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:42.020473+00:00
-- url     : https://prove2.me/theorems/0729fbd1-467e-4628-9c43-956572d7f0cb
-- title:
--   Lyndon: lt cases
-- statement:
--   The Lyndon construction uses the lt cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L190-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L190-L200

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

theorem GlobalTheory.Lyndon.lt_cases {u v : List A} (h : u < v) :
    (∀ x y, u ++ x < v ++ y) ∨ ∃ t, t ≠ [] ∧ v = u ++ t := by sorry
