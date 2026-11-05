-- Prove2me | Theorems.Thm_Groundwork_Grid_mixed_inj
-- name    : Groundwork.Grid.mixed_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:12.432454+00:00
-- url     : https://prove2.me/theorems/a601891a-675c-4fd1-b956-5b7603c43123
-- title:
--   Grid: mixed inj
-- statement:
--   x·n + y with y < n determines x and y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L28-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L28-L35

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

theorem Groundwork.Grid.mixed_inj {n x x' y y' : ℕ} (hy : y < n) (hy' : y' < n) (h : x * n + y = x' * n + y') : x = x' ∧ y = y' := by sorry
