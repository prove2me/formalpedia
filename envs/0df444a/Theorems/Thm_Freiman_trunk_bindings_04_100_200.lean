-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_04_100_200
-- name    : Freiman.trunk_bindings_04_100_200
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:48:56.045806+00:00
-- url     : https://prove2.me/theorems/79745ec0-2b12-41c6-a554-f76be3cb5d15
-- title:
--   trunk bindings 04 100 200
-- statement:
--   State ['2', '1'], grouped rows 100–199: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_04_100_200 :
    trunkBindingBatch 4 100 200 := by
  sorry
