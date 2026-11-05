-- Prove2me | Theorems.Thm_Groundwork_Grid_mixed_lt
-- name    : Groundwork.Grid.mixed_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:40.294095+00:00
-- url     : https://prove2.me/theorems/0e8139a9-7e9b-45be-a3d9-b8c443165fa9
-- title:
--   Grid: mixed lt
-- statement:
--   x·n + y < m·n for x < m and y < n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L38-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L38-L41

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

theorem Groundwork.Grid.mixed_lt {m n x y : ℕ} (hx : x < m) (hy : y < n) : x * n + y < m * n := by sorry
