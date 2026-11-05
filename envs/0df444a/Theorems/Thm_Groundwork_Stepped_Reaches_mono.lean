-- Prove2me | Theorems.Thm_Groundwork_Stepped_Reaches_mono
-- name    : Groundwork.Stepped.Reaches.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:20:12.343212+00:00
-- url     : https://prove2.me/theorems/24b09830-9667-40a4-a2a7-ad3c086967b8
-- title:
--   Reaches: mono
-- statement:
--   The Reaches construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L48-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L48-L54

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

theorem Groundwork.Stepped.Reaches.mono {M : Stepped α β} {S S' t t' : ℕ} {b : β} {s : M.σ} (h : M.Reaches S b s t)
    (ht : t ≤ t') (hS : S ≤ S') : M.Reaches S' b s t' := by sorry
