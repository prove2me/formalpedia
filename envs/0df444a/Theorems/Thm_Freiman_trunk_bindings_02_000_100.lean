-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_02_000_100
-- name    : Freiman.trunk_bindings_02_000_100
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:48:50.589141+00:00
-- url     : https://prove2.me/theorems/3ca04514-71ed-4f8c-a4ea-38f426c0cdf9
-- title:
--   trunk bindings 02 000 100
-- statement:
--   State ['1', '3'], grouped rows 0–99: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_02_000_100 :
    trunkBindingBatch 2 0 100 := by
  sorry
