-- Prove2me | Theorems.Thm_Groundwork_Grid_ZW_eq_sum
-- name    : Groundwork.Grid.ZW_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:20:47.503745+00:00
-- url     : https://prove2.me/theorems/76a58c38-6ee0-4584-86fd-865fefd7b1ff
-- title:
--   Grid: ZW eq sum
-- statement:
--   On words, the value Z is the sum of the terms Z_ι over all ι, each ι written by a number y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L120-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L120-L123

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

theorem Groundwork.Grid.ZW_eq_sum (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    Inst.ZW n [] Rm = ∑ y ∈ range ((n + 1) ^ nRect g), sideZ g n Rm y := by sorry
