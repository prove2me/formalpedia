-- Prove2me | Theorems.Thm_Freiman_trunk_select_late_parent_gluing
-- name    : Freiman.trunk_select_late_parent_gluing
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:03:37.79877+00:00
-- url     : https://prove2.me/theorems/00fc40c2-d546-428a-be95-e268475d9900
-- title:
--   trunk select late parent gluing
-- statement:
--   Original finite source-row selection and interval gluing for lower_late_parent_gluing. Use the recorded child geometry, parent suffix bounds, and exactly the passed J/early/late insertion theorem at its named source hole; these are combinatorial/interval obligations, not further numerical certificate assertions.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_select_late_parent_gluing (hroute : ∀ (t : ℝ) (p : LowerPair), lowerState t p → (¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) → lowerLateEntryDomain p → ∃ ls : List LowerLabel, lowerLateRouteValid p ls)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p)
    (hg : TrunkActiveGeometry p) :
    lowerNumericSuccessor t p := by
  sorry
