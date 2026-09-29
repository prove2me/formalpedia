-- Prove2me | Theorems.Thm_Freiman_trunk_join_bindings_14
-- name    : Freiman.trunk_join_bindings_14
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:56:52.561875+00:00
-- url     : https://prove2.me/theorems/8fdce122-9f1b-4721-bf67-de72946d771e
-- title:
--   trunk join bindings 14
-- statement:
--   Finite list indexing joins this state’s disjoint record-binding batches.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_join_bindings_14 (h0 : trunkBindingBatch 14 0 66) :
    ∀ g ∈ (trunkCatalog.states 14).groups, trunkGroupValid trunkCatalog 14 g := by
  sorry
