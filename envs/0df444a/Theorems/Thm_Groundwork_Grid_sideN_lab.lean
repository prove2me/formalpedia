-- Prove2me | Theorems.Thm_Groundwork_Grid_sideN_lab
-- name    : Groundwork.Grid.sideN_lab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:12.201406+00:00
-- url     : https://prove2.me/theorems/4c80a1ff-04af-4c39-94f3-4df5733afa2c
-- title:
--   Grid: side N lab
-- statement:
--   The labels of two parts are all words of that length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L201-L207
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L201-L207

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

theorem Groundwork.Grid.sideN_lab (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) {a b : Fin g} (hab : a ≠ b) :
    (sideN g tr n Rm y).lab a b = words (sideCap g tr n y a b) := by sorry
