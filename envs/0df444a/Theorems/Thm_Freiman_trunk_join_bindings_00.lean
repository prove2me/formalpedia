-- Prove2me | Theorems.Thm_Freiman_trunk_join_bindings_00
-- name    : Freiman.trunk_join_bindings_00
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:46:57.794414+00:00
-- url     : https://prove2.me/theorems/1e66dcc7-26ce-4544-a653-a0fb71ddac06
-- title:
--   trunk join bindings 00
-- statement:
--   Finite list indexing joins this state’s disjoint record-binding batches.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_join_bindings_00 (h0 : trunkBindingBatch 0 0 100) (h1 : trunkBindingBatch 0 100 200) (h2 : trunkBindingBatch 0 200 300) (h3 : trunkBindingBatch 0 300 400) (h4 : trunkBindingBatch 0 400 438) :
    ∀ g ∈ (trunkCatalog.states 0).groups, trunkGroupValid trunkCatalog 0 g := by
  sorry
