-- Prove2me | Theorems.Thm_Groundwork_Grid_sideN_sized
-- name    : Groundwork.Grid.sideN_sized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:05.275529+00:00
-- url     : https://prove2.me/theorems/55647b03-62d8-4cad-a4e4-47ec6fa81fc3
-- title:
--   Grid: side N sized
-- statement:
--   The network on words has size 2g³λ, and values of at most g·B + g²·λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L161-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L161-L164

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

theorem Groundwork.Grid.sideN_sized {g n B : ℕ} (tr : Bool) (hn : 1 ≤ n) {Rm : Inst (Fin (g * g)) (List Bool)} (hR : BoundedInst n B Rm)
    (y : ℕ) : (sideN g tr n Rm y).Sized (2 * g ^ 3 * n) (g * B + g ^ 2 * n) := by sorry
