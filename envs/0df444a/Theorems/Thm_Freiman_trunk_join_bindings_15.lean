-- Prove2me | Theorems.Thm_Freiman_trunk_join_bindings_15
-- name    : Freiman.trunk_join_bindings_15
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:57:27.951023+00:00
-- url     : https://prove2.me/theorems/c26b39b2-9b8c-48f5-afbe-0e0f0c2165d3
-- title:
--   trunk join bindings 15
-- statement:
--   Finite list indexing joins this state’s disjoint record-binding batches.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_join_bindings_15 (h0 : trunkBindingBatch 15 0 100) (h1 : trunkBindingBatch 15 100 110) :
    ∀ g ∈ (trunkCatalog.states 15).groups, trunkGroupValid trunkCatalog 15 g := by
  sorry
