-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_04_200_300
-- name    : Freiman.trunk_bindings_04_200_300
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:50:12.754648+00:00
-- url     : https://prove2.me/theorems/c96b278f-eba9-420a-90f0-e805e5c2ac53
-- title:
--   trunk bindings 04 200 300
-- statement:
--   State ['2', '1'], grouped rows 200–299: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_04_200_300 :
    trunkBindingBatch 4 200 300 := by
  sorry
