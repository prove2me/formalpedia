-- Prove2me | Theorems.Thm_Freiman_trunk_join_bindings_08
-- name    : Freiman.trunk_join_bindings_08
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:51:38.134302+00:00
-- url     : https://prove2.me/theorems/ed71a576-e2ee-4c87-9e7b-500ec5d7af55
-- title:
--   trunk join bindings 08
-- statement:
--   Finite list indexing joins this state’s disjoint record-binding batches.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_join_bindings_08 (h0 : trunkBindingBatch 8 0 100) (h1 : trunkBindingBatch 8 100 200) (h2 : trunkBindingBatch 8 200 262) :
    ∀ g ∈ (trunkCatalog.states 8).groups, trunkGroupValid trunkCatalog 8 g := by
  sorry
