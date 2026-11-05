-- Prove2me | Theorems.Thm_Groundwork_Grid_U_sideN_row
-- name    : Groundwork.Grid.U_sideN_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:01.913809+00:00
-- url     : https://prove2.me/theorems/336a4853-778b-4f1c-962b-8c38e3281969
-- title:
--   Grid: U side N row
-- statement:
--   The number of bits on the wires of the row network (every wire counted twice): the straight
--   edges (inside a row or a column),
--   and the cost `priceRow` of the rectangles.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L169-L174
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L169-L174

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)

theorem Groundwork.Grid.U_sideN_row (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) :
    (sideN g false n Rm y).U = g ^ 2 * (g - 1) * n + priceRow g n y := by sorry
