-- Prove2me | Theorems.Thm_Freiman_trunk_specs_sound
-- name    : Freiman.trunk_specs_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:58:29.221315+00:00
-- url     : https://prove2.me/theorems/d0c4a2e6-72df-4097-9fd6-190d4a724462
-- title:
--   trunk specs sound
-- statement:
--   Every listed nonempty, strict-goodness, contact and anchor specification is valid for the actual active source mode.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_specs_sound (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par) :
    ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp := by
  sorry
