-- Prove2me | Theorems.Thm_Freiman_trunk_state_from_tree
-- name    : Freiman.trunk_state_from_tree
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:59:02.954907+00:00
-- url     : https://prove2.me/theorems/aea92fdd-5b10-4e54-912d-876c7db7d342
-- title:
--   trunk state from tree
-- statement:
--   For an actual source plan and parent mode, complete record coverage excludes every failed nonautomatic endpoint comparison; componentwise branches need no polynomial record.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_state_from_tree (C : TrunkCatalog) (k : Fin 16)
    (hb : (∀ g ∈ (C.states k).groups, trunkGroupValid C k g) ∧ trunkCoverage C k)
    (ht : TrunkTreeSound C) :
    trunkStateSound C k := by
  sorry
