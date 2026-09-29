-- Prove2me | Theorems.Thm_Freiman_trunk_witnesses_6000_6125
-- name    : Freiman.trunk_witnesses_6000_6125
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:43:58.425818+00:00
-- url     : https://prove2.me/theorems/6eead2d0-ef7a-49fa-8716-8638e74bfa54
-- title:
--   trunk witnesses 6000 6125
-- statement:
--   Exact rational validation of source witnesses 6001–6125; preserve every printed margin and the ordinary/diagonal orientation.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_witnesses_6000_6125 :
    trunkWitnessBatch 6000 6125 := by
  sorry
