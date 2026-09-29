-- Prove2me | Theorems.Thm_Freiman_trunk_select_geometry_equal_small_left
-- name    : Freiman.trunk_select_geometry_equal_small_left
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:00:50.710112+00:00
-- url     : https://prove2.me/theorems/4c7721a3-5bf3-45c8-9df0-f9c96f757bcb
-- title:
--   trunk select geometry equal small left
-- statement:
--   Original finite source-row selection and interval gluing for lower_geometry_equal_small_left. Use the recorded child geometry, parent suffix bounds, and exactly the passed J/early/late insertion theorem at its named source hole; these are combinatorial/interval obligations, not further numerical certificate assertions.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_select_geometry_equal_small_left (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ lowerL p)
    (hg : TrunkActiveGeometry p) :
    lowerNumericSuccessor t p := by
  sorry
