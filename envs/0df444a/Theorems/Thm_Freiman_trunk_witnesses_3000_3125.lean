-- Prove2me | Theorems.Thm_Freiman_trunk_witnesses_3000_3125
-- name    : Freiman.trunk_witnesses_3000_3125
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:42:23.144979+00:00
-- url     : https://prove2.me/theorems/fe0b4049-b359-4cd6-a93a-28fdb67b6a42
-- title:
--   trunk witnesses 3000 3125
-- statement:
--   Exact rational validation of source witnesses 3001–3125; preserve every printed margin and the ordinary/diagonal orientation.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_witnesses_3000_3125 :
    trunkWitnessBatch 3000 3125 := by
  sorry
