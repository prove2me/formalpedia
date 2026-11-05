-- Prove2me | Theorems.Thm_Groundwork_size_int
-- name    : Groundwork.size_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:19:19.327454+00:00
-- url     : https://prove2.me/theorems/308d8958-6578-432c-a290-e55aaaa53ab8
-- title:
--   Groundwork: size int
-- statement:
--   The Groundwork construction uses the size int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L22-L22
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L22-L22

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
variable {α β : Type}

theorem Groundwork.size_int (z : ℤ) : size z = z.natAbs.size + 1 := by sorry

attribute [defeq] Groundwork.size_int
