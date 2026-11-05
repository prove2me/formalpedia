-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_mem_membersF
-- name    : Groundwork.Prog.NetE.mem_membersF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:47.630233+00:00
-- url     : https://prove2.me/theorems/9701db35-706c-437f-8f1d-eae73f647678
-- title:
--   Net E: mem members F
-- statement:
--   The Net E construction uses the mem members F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L116-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L116-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)

theorem Groundwork.Prog.NetE.mem_membersF (x G : ℕ) (a : Fin g) : a ∈ membersF K x G ↔ col K x a = G := by sorry
