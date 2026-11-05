-- Prove2me | Theorems.Thm_Groundwork_Stepped_next_iterate_of_out
-- name    : Groundwork.Stepped.next_iterate_of_out
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:09.849017+00:00
-- url     : https://prove2.me/theorems/1dad19b8-0cb9-4deb-8143-6912960f7b7e
-- title:
--   Stepped: next iterate of out
-- statement:
--   The Stepped construction uses the next iterate of out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L59-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L59-L63

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

theorem Groundwork.Stepped.next_iterate_of_out {M : Stepped α β} {s : M.σ} {b : β} (h : M.out s = some b) (n : ℕ) :
    M.next^[n] s = s := by sorry
