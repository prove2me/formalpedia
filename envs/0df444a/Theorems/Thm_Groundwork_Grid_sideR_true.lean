-- Prove2me | Theorems.Thm_Groundwork_Grid_sideR_true
-- name    : Groundwork.Grid.sideR_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:18:34.009443+00:00
-- url     : https://prove2.me/theorems/c07d48bc-fbcd-4cbf-876d-88692f8f10e9
-- title:
--   Grid: side R true
-- statement:
--   The instance on the transposed grid is the transpose of the instance on the grid.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L99-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L99-L100

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

theorem Groundwork.Grid.sideR_true (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : sideR g true n Rm = trInst (sideR g false n Rm) := by sorry
