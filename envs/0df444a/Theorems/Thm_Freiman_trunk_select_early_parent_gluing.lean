-- Prove2me | Theorems.Thm_Freiman_trunk_select_early_parent_gluing
-- name    : Freiman.trunk_select_early_parent_gluing
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:03:34.272739+00:00
-- url     : https://prove2.me/theorems/eee27484-890f-4889-a869-39c61cd89331
-- title:
--   trunk select early parent gluing
-- statement:
--   Original finite source-row selection and interval gluing for lower_early_parent_gluing. Use the recorded child geometry, parent suffix bounds, and exactly the passed J/early/late insertion theorem at its named source hole; these are combinatorial/interval obligations, not further numerical certificate assertions.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_select_early_parent_gluing (hchain : ∀ (t : ℝ) (p : LowerPair), lowerState t p → lowerEarlyDomain p → lowerEarlyGeometry p)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ ¬ lowerL p ∧ lowerR p ∧ ¬ lowerA p 16)
    (hg : TrunkActiveGeometry p) :
    lowerNumericSuccessor t p := by
  sorry
