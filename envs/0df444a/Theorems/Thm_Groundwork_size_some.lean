-- Prove2me | Theorems.Thm_Groundwork_size_some
-- name    : Groundwork.size_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:19:55.846904+00:00
-- url     : https://prove2.me/theorems/962bcf97-88fc-4ae8-9b32-85e8eeedc8f7
-- title:
--   Groundwork: size some
-- statement:
--   The Groundwork construction uses the size some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L29-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L29-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
variable {α β : Type}

theorem Groundwork.size_some [HasSize α] (a : α) : size (some a) = size a + 1 := by sorry

attribute [defeq] Groundwork.size_some
