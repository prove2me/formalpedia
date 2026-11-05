-- Prove2me | Theorems.Thm_Groundwork_Grid_nRect_eq
-- name    : Groundwork.Grid.nRect_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:24.019631+00:00
-- url     : https://prove2.me/theorems/40dfc7e6-507d-4d84-adaf-15414a57f90a
-- title:
--   Grid: n Rect eq
-- statement:
--   The number of rectangles is the square of the number of pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L57-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L57-L59

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

theorem Groundwork.Grid.nRect_eq (g : ℕ) : nRect g = c2 g * c2 g := by sorry
