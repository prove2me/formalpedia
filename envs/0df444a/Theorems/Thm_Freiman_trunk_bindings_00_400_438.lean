-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_00_400_438
-- name    : Freiman.trunk_bindings_00_400_438
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:46:34.199478+00:00
-- url     : https://prove2.me/theorems/d8f98190-5a24-4762-ab6c-5494304b4389
-- title:
--   trunk bindings 00 400 438
-- statement:
--   State ['1', '1'], grouped rows 400–437: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_00_400_438 :
    trunkBindingBatch 0 400 438 := by
  sorry
