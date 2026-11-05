-- Prove2me | Theorems.Thm_Groundwork_Prog_sideA_mul
-- name    : Groundwork.Prog.sideA_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:10:34.16456+00:00
-- url     : https://prove2.me/theorems/cc671459-c9c2-4b2f-a544-4f6d1f25d181
-- title:
--   Prog: side A mul
-- statement:
--   The Prog construction uses the side A mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L123-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L123-L125

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

theorem Groundwork.Prog.sideA_mul (g X : ℕ) :
    sideA g * X = 4 * (g ^ 4 * X) + 8 * (g ^ 3 * X) + 20 * (g ^ 2 * X) + 20 * (g * X) + 1000 * X := by sorry
