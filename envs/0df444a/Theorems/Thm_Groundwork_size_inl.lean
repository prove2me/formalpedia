-- Prove2me | Theorems.Thm_Groundwork_size_inl
-- name    : Groundwork.size_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:19:29.143896+00:00
-- url     : https://prove2.me/theorems/55285c8e-6df8-42ce-9456-26b0aed03394
-- title:
--   Groundwork: size inl
-- statement:
--   The Groundwork construction uses the size inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L26-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L26-L26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
variable {α β : Type}

theorem Groundwork.size_inl [HasSize α] [HasSize β] (a : α) : size (Sum.inl a : α ⊕ β) = size a + 1 := by sorry

attribute [defeq] Groundwork.size_inl
