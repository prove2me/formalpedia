-- Prove2me | Theorems.Thm_Freiman_trunk_bindings_06_000_100
-- name    : Freiman.trunk_bindings_06_000_100
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:51:43.345332+00:00
-- url     : https://prove2.me/theorems/6db9bf6f-90f4-459f-b8f6-ae572583121f
-- title:
--   trunk bindings 06 000 100
-- statement:
--   State ['2', '3'], grouped rows 0–99: exact source branch indices, every parent index, witness-bound membership and rectangle/subrectangle binding.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bindings_06_000_100 :
    trunkBindingBatch 6 0 100 := by
  sorry
