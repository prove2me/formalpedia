-- Prove2me | Theorems.Thm_Freiman_trunk_join_bindings_05
-- name    : Freiman.trunk_join_bindings_05
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:50:17.400781+00:00
-- url     : https://prove2.me/theorems/c5b14b59-cff3-41f7-84cb-93af6653d957
-- title:
--   trunk join bindings 05
-- statement:
--   Finite list indexing joins this state’s disjoint record-binding batches.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_join_bindings_05 (h0 : trunkBindingBatch 5 0 100) (h1 : trunkBindingBatch 5 100 200) (h2 : trunkBindingBatch 5 200 300) (h3 : trunkBindingBatch 5 300 400) (h4 : trunkBindingBatch 5 400 428) :
    ∀ g ∈ (trunkCatalog.states 5).groups, trunkGroupValid trunkCatalog 5 g := by
  sorry
