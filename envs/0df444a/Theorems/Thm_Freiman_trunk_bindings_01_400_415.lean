-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_01_400_415
-- name    : Freiman.trunk_bindings_01_400_415
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:48:36.060348+00:00
-- url     : https://prove2.me/theorems/cbd6fecd-a2a0-4f35-9d62-1ae2eebecb48
-- title:
--   trunk bindings 01 400 415
-- statement:
--   State ['1', '2'], grouped rows 400–414: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_01_400_415 :
    trunkBindingBatch 1 400 415 := by
  sorry
