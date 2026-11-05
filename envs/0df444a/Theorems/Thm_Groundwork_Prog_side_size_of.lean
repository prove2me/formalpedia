-- Prove2me | Theorems.Thm_Groundwork_Prog_side_size_of
-- name    : Groundwork.Prog.side_size_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:10:42.534193+00:00
-- url     : https://prove2.me/theorems/6fb727dc-82ba-4c31-990d-8993084131a5
-- title:
--   Prog: side size of
-- statement:
--   A size that is linear in size c + B + λ, beside S, is within the bound.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L128-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L128-L129

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

theorem Groundwork.Prog.side_size_of {g S X Z : ℕ} (h : Z ≤ S + sideA g * X) : Z ≤ S + sideA g * X ^ sideA g := by sorry
