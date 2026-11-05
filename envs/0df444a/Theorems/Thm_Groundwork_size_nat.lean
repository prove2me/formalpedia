-- Prove2me | Theorems.Thm_Groundwork_size_nat
-- name    : Groundwork.size_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:19:10.112221+00:00
-- url     : https://prove2.me/theorems/6aca5363-6fb7-472d-9085-0b40e7b56519
-- title:
--   Groundwork: size nat
-- statement:
--   The Groundwork construction uses the size nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L21-L21
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L21-L21

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
variable {α β : Type}

theorem Groundwork.size_nat (n : ℕ) : size n = n.size + 1 := by sorry

attribute [defeq] Groundwork.size_nat
