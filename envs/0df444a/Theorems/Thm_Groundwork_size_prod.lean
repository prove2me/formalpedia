-- Prove2me | Theorems.Thm_Groundwork_size_prod
-- name    : Groundwork.size_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:19:18.54019+00:00
-- url     : https://prove2.me/theorems/4a26d70c-ee79-448e-a763-07c2c7032524
-- title:
--   Groundwork: size prod
-- statement:
--   The Groundwork construction uses the size prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L25-L25
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L25-L25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
variable {α β : Type}

theorem Groundwork.size_prod [HasSize α] [HasSize β] (p : α × β) : size p = size p.1 + size p.2 := by sorry

attribute [defeq] Groundwork.size_prod
