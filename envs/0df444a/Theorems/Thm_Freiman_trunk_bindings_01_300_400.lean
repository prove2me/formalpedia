-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_01_300_400
-- name    : Freiman.trunk_bindings_01_300_400
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:47:32.406162+00:00
-- url     : https://prove2.me/theorems/f04540fe-42bb-47f6-920e-061231220469
-- title:
--   trunk bindings 01 300 400
-- statement:
--   State ['1', '2'], grouped rows 300–399: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_01_300_400 :
    trunkBindingBatch 1 300 400 := by
  sorry
