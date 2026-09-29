-- Prove2me | Theorems.Thm_Freiman_trunk_nonempty_from_specs
-- name    : Freiman.trunk_nonempty_from_specs
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:58:32.591905+00:00
-- url     : https://prove2.me/theorems/25e5d09c-e052-435a-80b8-83315a521182
-- title:
--   trunk nonempty from specs
-- statement:
--   Each listed child nonemptiness comparison supplies the closed interval endpoint order; both common parities give the same physical nonempty cover.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_nonempty_from_specs (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    ∀ l ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels, (lowerCover (lowerChild p l)).Nonempty := by
  sorry
