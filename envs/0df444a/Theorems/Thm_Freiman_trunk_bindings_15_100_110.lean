-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_15_100_110
-- name    : Freiman.trunk_bindings_15_100_110
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:03:08.866075+00:00
-- url     : https://prove2.me/theorems/b2f04161-662b-4cd5-9400-f949c52a8cac
-- title:
--   trunk bindings 15 100 110
-- statement:
--   State ['31', '31'], grouped rows 100–109: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_15_100_110 :
    trunkBindingBatch 15 100 110 := by
  sorry
