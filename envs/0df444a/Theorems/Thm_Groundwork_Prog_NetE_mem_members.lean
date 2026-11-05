-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_mem_members
-- name    : Groundwork.Prog.NetE.mem_members
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:08.657193+00:00
-- url     : https://prove2.me/theorems/42966960-b634-40c8-ae78-a3c566f5b4f0
-- title:
--   Net E: mem members
-- statement:
--   The Net E construction uses the mem members property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L24-L25
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L24-L25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)

theorem Groundwork.Prog.NetE.mem_members {x G a : ℕ} : a ∈ members K g x G ↔ a < g ∧ col K x a = G := by sorry
