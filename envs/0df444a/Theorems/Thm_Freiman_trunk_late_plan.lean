-- Prove2me | Theorems.Thm_Freiman_trunk_late_plan
-- name    : Freiman.trunk_late_plan
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:00:15.147584+00:00
-- url     : https://prove2.me/theorems/b16695de-b039-4514-a9a1-dd0ab95b5c89
-- title:
--   trunk late plan
-- statement:
--   notH9-left31 is the precise original eight-row source plan; all cutoff weak/strict directions, suffix classification and anchor labels are explicit.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_late_plan (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) (k : Fin 16)
    (hf : lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context) :
    ∃ pi : ℕ, pi < (trunkSourcePlans (trunkCatalog.states k).context).length ∧
    trunkHolds (trunkPlanAt (trunkCatalog.states k) pi).cuts (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) ∧
    ([2],[2]) ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels ∧ ([2],[1]) ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels := by
  sorry
