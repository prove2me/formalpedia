-- Prove2me | Theorems.Thm_Groundwork_Prog_size_pattern_le
-- name    : Groundwork.Prog.size_pattern_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:10:36.8626+00:00
-- url     : https://prove2.me/theorems/41a5e128-9f1a-42a4-82df-b891882410f3
-- title:
--   Prog: size pattern le
-- statement:
--   The size of the number y that encodes the pattern ι ∈ {0,…,n}^R of one level of the recursion,
--   with R = `nRect g` rectangles.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L133-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L133-L142

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)

theorem Groundwork.Prog.size_pattern_le {g n y : ℕ} (hy : y < (n + 1) ^ nRect g) : size y ≤ g ^ 4 * n + 1 := by sorry
