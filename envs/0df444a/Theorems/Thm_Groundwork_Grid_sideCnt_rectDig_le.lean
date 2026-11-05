-- Prove2me | Theorems.Thm_Groundwork_Grid_sideCnt_rectDig_le
-- name    : Groundwork.Grid.sideCnt_rectDig_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:07:16.001104+00:00
-- url     : https://prove2.me/theorems/b375149d-969a-4292-9911-cb8a4c2d2190
-- title:
--   Grid: side Cnt rect Dig le
-- statement:
--   A label of a rectangle has at most n states other than the frequent one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L35-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L35-L38

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

theorem Groundwork.Grid.sideCnt_rectDig_le (g : ℕ) (tr : Bool) (n y p κ : ℕ) : sideCnt tr n (rectDig g tr n y p κ) ≤ n := by sorry
