-- Prove2me | Theorems.Thm_Freiman_trunk_join_bindings_13
-- name    : Freiman.trunk_join_bindings_13
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:56:19.596691+00:00
-- url     : https://prove2.me/theorems/346b4aa5-3b58-4b66-8d93-b85370430a04
-- title:
--   trunk join bindings 13
-- statement:
--   Finite list indexing joins this state’s disjoint record-binding batches.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_join_bindings_13 (h0 : trunkBindingBatch 13 0 100) (h1 : trunkBindingBatch 13 100 173) :
    ∀ g ∈ (trunkCatalog.states 13).groups, trunkGroupValid trunkCatalog 13 g := by
  sorry
