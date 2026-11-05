-- Prove2me | Theorems.Thm_Groundwork_size_list
-- name    : Groundwork.size_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:19:21.659196+00:00
-- url     : https://prove2.me/theorems/536b06a2-995d-4f0b-bd9d-efe211c80504
-- title:
--   Groundwork: size list
-- statement:
--   The Groundwork construction uses the size list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L30-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L30-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
variable {α β : Type}

theorem Groundwork.size_list [HasSize α] (l : List α) :
    size l = (l.map fun x => size x + 1).sum + 1 := by sorry

attribute [defeq] Groundwork.size_list
