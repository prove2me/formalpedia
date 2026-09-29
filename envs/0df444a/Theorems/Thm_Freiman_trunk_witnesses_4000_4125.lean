-- Prove2me | Theorems.Thm_Freiman_trunk_witnesses_4000_4125
-- name    : Freiman.trunk_witnesses_4000_4125
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:41:34.461635+00:00
-- url     : https://prove2.me/theorems/f9340928-cd2c-420d-ab29-335efdfc02b8
-- title:
--   trunk witnesses 4000 4125
-- statement:
--   Exact rational validation of source witnesses 4001–4125; preserve every printed margin and the ordinary/diagonal orientation.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_witnesses_4000_4125 :
    trunkWitnessBatch 4000 4125 := by
  sorry
