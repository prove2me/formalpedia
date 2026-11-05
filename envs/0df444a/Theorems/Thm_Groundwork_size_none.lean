-- Prove2me | Theorems.Thm_Groundwork_size_none
-- name    : Groundwork.size_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:19:18.084437+00:00
-- url     : https://prove2.me/theorems/c3baa479-8f5d-4b9b-a609-0ad640593dc7
-- title:
--   Groundwork: size none
-- statement:
--   The Groundwork construction uses the size none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L28-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L28-L28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
variable {α β : Type}

theorem Groundwork.size_none [HasSize α] : size (none : Option α) = 1 := by sorry

attribute [defeq] Groundwork.size_none
