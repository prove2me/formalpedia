-- Prove2me | Theorems.Thm_Groundwork_size_bool
-- name    : Groundwork.size_bool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:19:21.700455+00:00
-- url     : https://prove2.me/theorems/ad2f6365-6ec8-4a5c-977e-34dc89f096c6
-- title:
--   Groundwork: size bool
-- statement:
--   The Groundwork construction uses the size bool property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L23-L23
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L23-L23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
variable {α β : Type}

theorem Groundwork.size_bool (b : Bool) : size b = 1 := by sorry

attribute [defeq] Groundwork.size_bool
