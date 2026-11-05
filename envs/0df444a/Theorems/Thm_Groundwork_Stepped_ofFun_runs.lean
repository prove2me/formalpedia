-- Prove2me | Theorems.Thm_Groundwork_Stepped_ofFun_runs
-- name    : Groundwork.Stepped.ofFun_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:23:29.317223+00:00
-- url     : https://prove2.me/theorems/bfc231f7-cbdb-45d8-887e-c0707422f4d5
-- title:
--   Stepped: of Fun runs
-- statement:
--   The Stepped construction uses the of Fun runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L120-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L120-L122

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

theorem Groundwork.Stepped.ofFun_runs [HasSize α] [HasSize β] (f : α → β) (a : α) :
    (ofFun f).Runs a 1 (max (size a) (size (f a)) + 1) (f a) := by sorry
