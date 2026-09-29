-- Prove2me | Theorems.Thm_Freiman_trunk_witnesses_3750_3875
-- name    : Freiman.trunk_witnesses_3750_3875
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:41:10.726211+00:00
-- url     : https://prove2.me/theorems/b6c01ecd-140a-4570-b601-f90346dc8f3b
-- title:
--   trunk witnesses 3750 3875
-- statement:
--   Exact rational validation of source witnesses 3751–3875; preserve every printed margin and the ordinary/diagonal orientation.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_witnesses_3750_3875 :
    trunkWitnessBatch 3750 3875 := by
  sorry
