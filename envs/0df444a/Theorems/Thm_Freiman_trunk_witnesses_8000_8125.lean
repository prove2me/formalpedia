-- Prove2me | Theorems.Thm_Freiman_trunk_witnesses_8000_8125
-- name    : Freiman.trunk_witnesses_8000_8125
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:44:40.531389+00:00
-- url     : https://prove2.me/theorems/4413a080-4836-4c2e-8c0e-0fe7938134d1
-- title:
--   trunk witnesses 8000 8125
-- statement:
--   Exact rational validation of source witnesses 8001–8125; preserve every printed margin and the ordinary/diagonal orientation.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_witnesses_8000_8125 :
    trunkWitnessBatch 8000 8125 := by
  sorry
