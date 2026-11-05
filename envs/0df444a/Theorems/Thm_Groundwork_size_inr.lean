-- Prove2me | Theorems.Thm_Groundwork_size_inr
-- name    : Groundwork.size_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:19:24.654031+00:00
-- url     : https://prove2.me/theorems/f0c483ec-9456-4538-a4af-28a356c7e47f
-- title:
--   Groundwork: size inr
-- statement:
--   The Groundwork construction uses the size inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L27-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L27-L27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
variable {α β : Type}

theorem Groundwork.size_inr [HasSize α] [HasSize β] (b : β) : size (Sum.inr b : α ⊕ β) = size b + 1 := by sorry

attribute [defeq] Groundwork.size_inr
