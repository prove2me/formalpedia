-- Prove2me | Theorems.Thm_Groundwork_Prog_side_size_W
-- name    : Groundwork.Prog.side_size_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:05.283219+00:00
-- url     : https://prove2.me/theorems/bc210b1d-fb4a-4bad-a0cb-95449a41bcf4
-- title:
--   Prog: side size W
-- statement:
--   The sizes of the weights.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L145-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L145-L158

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

theorem Groundwork.Prog.side_size_W {C : Type} [HasSize C] (g B S lm : ℕ) (hl : 1 ≤ lm) (c : C) {y a : ℕ} {z : List Bool}
    (hy : y < (lm + 1) ^ nRect g) (ha : a < g) (hz : z.length = g ^ 3 * lm) :
    size ((c, y), (a, z)) + size g + (B * g + 2) + S + 3 ≤ S + sideA g * (size c + B + lm) ^ sideA g := by sorry
