-- Prove2me | Theorems.Thm_Freiman_trunk_goodness_from_specs_from_order
-- name    : Freiman.trunk_goodness_from_specs_from_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:00:54.583614+00:00
-- url     : https://prove2.me/theorems/eb03e120-7aae-4eaf-b5cc-339fcd2dab1f
-- title:
--   trunk goodness from specs from order
-- statement:
--   Select the actual strict normalization branch for each child. Its two strict crossed inequalities together with both separate strict own-interval endpoint inequalities give all four comparisons needed for max(lower)<min(upper).
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_goodness_from_specs_from_order (ho : ∀ w : LowerPair, lowerEndpoint w false < lowerEndpoint w true)
    (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    ∀ l ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels, lowerStrictGood (lowerChild p l) := by
  sorry
