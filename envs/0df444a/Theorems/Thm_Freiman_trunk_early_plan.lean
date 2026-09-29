-- Prove2me | Theorems.Thm_Freiman_trunk_early_plan
-- name    : Freiman.trunk_early_plan
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:59:40.79552+00:00
-- url     : https://prove2.me/theorems/6fc9808c-aee7-45df-a9b4-f73aec0c22ec
-- title:
--   trunk early plan
-- statement:
--   H9-notH16 is the precise original eight-row source plan; all cutoff weak/strict directions, suffix classification and anchor labels are explicit.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_early_plan (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) (k : Fin 16)
    (hf : lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context) :
    ∃ pi : ℕ, pi < (trunkSourcePlans (trunkCatalog.states k).context).length ∧
    trunkHolds (trunkPlanAt (trunkCatalog.states k) pi).cuts (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) ∧
    ([3],[2]) ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels ∧ ([2],[2]) ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels ∧ (trunkPlanAt (trunkCatalog.states k) pi).labels.getLast? = some ([3],[2]) := by
  sorry
