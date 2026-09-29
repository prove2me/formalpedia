-- Prove2me | Theorems.Thm_Freiman_trunk_late_geometry
-- name    : Freiman.trunk_late_geometry
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:00:20.014066+00:00
-- url     : https://prove2.me/theorems/844c2cc1-ff75-447c-b82b-031ac31de309
-- title:
--   trunk late geometry
-- statement:
--   Select the exact active source plan containing both inherited anchors.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_late_geometry (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) :
    ∃ plan : TrunkPlan, TrunkGeometry p plan ∧ ([2],[2]) ∈ plan.labels ∧ ([2],[1]) ∈ plan.labels := by
  sorry
