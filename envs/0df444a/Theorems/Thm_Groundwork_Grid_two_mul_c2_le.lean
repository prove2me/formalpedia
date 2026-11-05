-- Prove2me | Theorems.Thm_Groundwork_Grid_two_mul_c2_le
-- name    : Groundwork.Grid.two_mul_c2_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:46.816559+00:00
-- url     : https://prove2.me/theorems/537570f2-4ce1-46ad-87f6-ed53662e683f
-- title:
--   Grid: two mul c2 le
-- statement:
--   There are at most g²/2 pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L62-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L62-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)

theorem Groundwork.Grid.two_mul_c2_le (g : ℕ) : 2 * c2 g ≤ g ^ 2 := by sorry
