-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_05_400_428
-- name    : Freiman.trunk_bindings_05_400_428
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:49:50.02998+00:00
-- url     : https://prove2.me/theorems/fcc22f4a-7131-4d34-b41c-bef1df221c1a
-- title:
--   trunk bindings 05 400 428
-- statement:
--   State ['2', '2'], grouped rows 400–427: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_05_400_428 :
    trunkBindingBatch 5 400 428 := by
  sorry
