-- Prove2me | Theorems.Thm_Groundwork_Grid_rectLen_le
-- name    : Groundwork.Grid.rectLen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:07:11.914668+00:00
-- url     : https://prove2.me/theorems/3d1e010e-b00b-4302-9737-a172bcdc608d
-- title:
--   Grid: rect Len le
-- statement:
--   A chunk has at most 3n + 1 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L41-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L41-L45

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

theorem Groundwork.Grid.rectLen_le (g : ℕ) (tr : Bool) (n y p κ : ℕ) : rectLen g tr n y p κ ≤ 3 * n + 1 := by sorry
