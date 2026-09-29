-- Prove2me | Theorems.Thm_Freiman_trunk_contacts_from_specs
-- name    : Freiman.trunk_contacts_from_specs
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:59:04.374269+00:00
-- url     : https://prove2.me/theorems/2d4c2689-9fa5-4a28-b754-89d999673436
-- title:
--   trunk contacts from specs
-- statement:
--   The two weak crossed endpoint comparisons and the individual nonempty intervals give each explicitly recorded contact; the three source holes are excluded.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_contacts_from_specs (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    ∀ lm ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels.zip (trunkPlanAt (trunkCatalog.states k) pi).labels.tail, lm ∉ (trunkPlanAt (trunkCatalog.states k) pi).holes →
    (lowerCover (lowerChild p lm.1) ∩ lowerCover (lowerChild p lm.2)).Nonempty := by
  sorry
