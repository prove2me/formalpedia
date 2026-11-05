-- Prove2me | Theorems.Thm_Groundwork_Grid_mixed_surj
-- name    : Groundwork.Grid.mixed_surj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:44.838203+00:00
-- url     : https://prove2.me/theorems/366831cc-41fd-4e57-a0d3-af38f9e2a9aa
-- title:
--   Grid: mixed surj
-- statement:
--   Every number below m·n is x·n + y with x < m and y < n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L44-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L44-L49

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

theorem Groundwork.Grid.mixed_surj {m n z : ℕ} (h : z < m * n) : ∃ x < m, ∃ y < n, x * n + y = z := by sorry
