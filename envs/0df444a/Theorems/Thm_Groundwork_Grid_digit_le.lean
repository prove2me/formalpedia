-- Prove2me | Theorems.Thm_Groundwork_Grid_digit_le
-- name    : Groundwork.Grid.digit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:28:52.927426+00:00
-- url     : https://prove2.me/theorems/997444ff-5cf9-456b-aa82-315324d67411
-- title:
--   Grid: digit le
-- statement:
--   A digit in base n + 1 is at most n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L116-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L116-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits
import Theorems.Thm_Groundwork_Prog_digit_le

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)

theorem Groundwork.Grid.digit_le (n y q : ℕ) : digit n y q ≤ n := by sorry
