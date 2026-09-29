-- Prove2me | Theorems.Thm_Freiman_trunk_join_bindings_03
-- name    : Freiman.trunk_join_bindings_03
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:48:50.389786+00:00
-- url     : https://prove2.me/theorems/c9cdd201-84fe-49b5-aac1-9e1577271718
-- title:
--   trunk join bindings 03
-- statement:
--   Finite list indexing joins this state’s disjoint record-binding batches.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_join_bindings_03 (h0 : trunkBindingBatch 3 0 100) (h1 : trunkBindingBatch 3 100 200) (h2 : trunkBindingBatch 3 200 213) :
    ∀ g ∈ (trunkCatalog.states 3).groups, trunkGroupValid trunkCatalog 3 g := by
  sorry
