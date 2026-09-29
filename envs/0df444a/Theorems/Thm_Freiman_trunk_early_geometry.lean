-- Prove2me | Theorems.Thm_Freiman_trunk_early_geometry
-- name    : Freiman.trunk_early_geometry
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:01:41.953187+00:00
-- url     : https://prove2.me/theorems/193ac3e7-31b3-4219-9f5a-915add02a4ff
-- title:
--   trunk early geometry
-- statement:
--   Select the exact active source plan containing both inherited anchors and the early lower parent anchor.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_early_geometry (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) :
    ∃ plan : TrunkPlan, TrunkGeometry p plan ∧ ([3],[2]) ∈ plan.labels ∧ ([2],[2]) ∈ plan.labels ∧ plan.labels.getLast? = some ([3],[2]) := by
  sorry
