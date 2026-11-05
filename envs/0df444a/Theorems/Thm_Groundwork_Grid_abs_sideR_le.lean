-- Prove2me | Theorems.Thm_Groundwork_Grid_abs_sideR_le
-- name    : Groundwork.Grid.abs_sideR_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:12.754329+00:00
-- url     : https://prove2.me/theorems/24642ba1-666d-4340-841d-6f49edec59eb
-- title:
--   Grid: abs side R le
-- statement:
--   The bound 2^B on the instance at the queries that are asked passes to the grid.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L121-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L121-L129

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset

theorem Groundwork.Grid.abs_sideR_le {g n B : ℕ} (tr : Bool) {Rm : Inst (Fin (g * g)) (List Bool)} (hR : Prog.BoundedInst n B Rm)
    (w : Fin g × Fin g) (h : Fin g × Fin g → Bits n) : |sideR g tr n Rm w h| ≤ 2 ^ B := by sorry
