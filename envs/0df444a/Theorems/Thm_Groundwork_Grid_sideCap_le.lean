-- Prove2me | Theorems.Thm_Groundwork_Grid_sideCap_le
-- name    : Groundwork.Grid.sideCap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:10.469202+00:00
-- url     : https://prove2.me/theorems/01c4242e-01f7-4986-b9f7-55e9ea0b3666
-- title:
--   Grid: side Cap le
-- statement:
--   Labels have at most g·λ + 2g²·λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L210-L218
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L210-L218

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

theorem Groundwork.Grid.sideCap_le {g n : ℕ} (tr : Bool) (hn : 1 ≤ n) (y a b : ℕ) : sideCap g tr n y a b ≤ g * n + 2 * g ^ 2 * n := by sorry
