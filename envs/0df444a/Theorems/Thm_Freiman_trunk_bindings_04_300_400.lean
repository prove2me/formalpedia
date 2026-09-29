-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_04_300_400
-- name    : Freiman.trunk_bindings_04_300_400
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:50:22.127608+00:00
-- url     : https://prove2.me/theorems/932ea528-2343-4f08-8b90-77740013fb6d
-- title:
--   trunk bindings 04 300 400
-- statement:
--   State ['2', '1'], grouped rows 300–399: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_04_300_400 :
    trunkBindingBatch 4 300 400 := by
  sorry
