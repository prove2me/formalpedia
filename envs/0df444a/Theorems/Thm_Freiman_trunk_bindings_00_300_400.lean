-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_00_300_400
-- name    : Freiman.trunk_bindings_00_300_400
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:46:30.982071+00:00
-- url     : https://prove2.me/theorems/a674a930-2794-4235-9d3c-468a15794a4c
-- title:
--   trunk bindings 00 300 400
-- statement:
--   State ['1', '1'], grouped rows 300–399: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_00_300_400 :
    trunkBindingBatch 0 300 400 := by
  sorry
