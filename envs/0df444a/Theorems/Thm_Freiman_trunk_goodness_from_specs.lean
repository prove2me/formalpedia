-- Prove2me | Theorems.Thm_Freiman_trunk_goodness_from_specs
-- name    : Freiman.trunk_goodness_from_specs
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:59:01.396998+00:00
-- url     : https://prove2.me/theorems/df92325b-c73e-43e8-bfa4-53fcb05aa039
-- title:
--   trunk goodness from specs
-- statement:
--   The source strict-goodness records yield the existing max<min definition, explicitly using strict own-endpoint order and the two crossed inequalities.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_goodness_from_specs (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    ∀ l ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels, lowerStrictGood (lowerChild p l) := by
  sorry
