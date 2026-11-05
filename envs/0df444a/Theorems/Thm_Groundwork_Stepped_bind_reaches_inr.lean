-- Prove2me | Theorems.Thm_Groundwork_Stepped_bind_reaches_inr
-- name    : Groundwork.Stepped.bind_reaches_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:58.090121+00:00
-- url     : https://prove2.me/theorems/3e9f1abe-9c22-4776-85ce-b4461afd1800
-- title:
--   Stepped: bind reaches inr
-- statement:
--   The Stepped construction uses the bind reaches inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L169-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L169-L173

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}

theorem Groundwork.Stepped.bind_reaches_inr [HasSize α] {M : Stepped α β} {N : Stepped (α × β) γ} {S t : ℕ} {c : γ} {s : N.σ}
    (h : N.Reaches S c s t) : (bind M N).Reaches (S + 1) c (.inr s) t := by sorry
