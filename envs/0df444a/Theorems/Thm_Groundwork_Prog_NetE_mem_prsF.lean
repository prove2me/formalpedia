-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_mem_prsF
-- name    : Groundwork.Prog.NetE.mem_prsF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:12.823503+00:00
-- url     : https://prove2.me/theorems/fa3f79c7-659f-4b36-8237-40d79675b0ce
-- title:
--   Net E: mem prs F
-- statement:
--   The Net E construction uses the mem prs F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L129-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L129-L132

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

theorem Groundwork.Prog.NetE.mem_prsF (x G G' : ℕ) (p : Fin g × Fin g) :
    p ∈ prsF K x G G' ↔ col K x p.1 = G ∧ col K x p.2 = G' := by sorry
