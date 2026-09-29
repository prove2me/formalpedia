-- Prove2me | Theorems.Thm_Freiman_trunk_join_bindings_04
-- name    : Freiman.trunk_join_bindings_04
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:49:18.290962+00:00
-- url     : https://prove2.me/theorems/a230834e-c180-4370-8b32-c3382adce631
-- title:
--   trunk join bindings 04
-- statement:
--   Finite list indexing joins this state’s disjoint record-binding batches.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_join_bindings_04 (h0 : trunkBindingBatch 4 0 100) (h1 : trunkBindingBatch 4 100 200) (h2 : trunkBindingBatch 4 200 300) (h3 : trunkBindingBatch 4 300 400) (h4 : trunkBindingBatch 4 400 416) :
    ∀ g ∈ (trunkCatalog.states 4).groups, trunkGroupValid trunkCatalog 4 g := by
  sorry
