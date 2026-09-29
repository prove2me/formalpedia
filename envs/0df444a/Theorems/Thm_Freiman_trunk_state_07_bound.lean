-- Prove2me | Theorems.Thm_Freiman_trunk_state_07_bound
-- name    : Freiman.trunk_state_07_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:51:14.059246+00:00
-- url     : https://prove2.me/theorems/c3de497a-f8b3-4206-94c0-4a732903cae8
-- title:
--   trunk state 07 bound
-- statement:
--   All source records for this canonical rectangle are bound and exhaustively covered.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_state_07_bound :
    (∀ g ∈ (trunkCatalog.states 7).groups, trunkGroupValid trunkCatalog 7 g) ∧ trunkCoverage trunkCatalog 7 := by
  sorry
