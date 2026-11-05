-- Prove2me | Theorems.Thm_Groundwork_Grid_ixOf_bijOn
-- name    : Groundwork.Grid.ixOf_bijOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:24.879259+00:00
-- url     : https://prove2.me/theorems/2a6a9031-1dfa-4ba4-86aa-63a6ec3f15a8
-- title:
--   Grid: ix Of bij On
-- statement:
--   The rectangles get the numbers below nRect g, each number once.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L76-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L76-L97

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

theorem Groundwork.Grid.ixOf_bijOn (g : ℕ) : Set.BijOn (ixOf g) (Ω (Fin g) (Fin g)) (range (nRect g)) := by sorry
