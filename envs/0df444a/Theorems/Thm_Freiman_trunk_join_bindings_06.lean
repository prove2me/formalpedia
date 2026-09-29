-- Prove2me | Theorems.Thm_Freiman_trunk_join_bindings_06
-- name    : Freiman.trunk_join_bindings_06
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:50:46.591908+00:00
-- url     : https://prove2.me/theorems/e28fa7d4-2ff6-4afe-8b18-da91e1e04866
-- title:
--   trunk join bindings 06
-- statement:
--   Finite list indexing joins this state’s disjoint record-binding batches.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_join_bindings_06 (h0 : trunkBindingBatch 6 0 100) (h1 : trunkBindingBatch 6 100 185) :
    ∀ g ∈ (trunkCatalog.states 6).groups, trunkGroupValid trunkCatalog 6 g := by
  sorry
