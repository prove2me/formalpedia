-- Prove2me | Theorems.Thm_Freiman_trunk_join_bindings_09
-- name    : Freiman.trunk_join_bindings_09
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:52:28.801352+00:00
-- url     : https://prove2.me/theorems/cbff62fe-fdcf-4db7-b802-def2b431cc36
-- title:
--   trunk join bindings 09
-- statement:
--   Finite list indexing joins this state’s disjoint record-binding batches.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_join_bindings_09 (h0 : trunkBindingBatch 9 0 100) (h1 : trunkBindingBatch 9 100 200) (h2 : trunkBindingBatch 9 200 260) :
    ∀ g ∈ (trunkCatalog.states 9).groups, trunkGroupValid trunkCatalog 9 g := by
  sorry
