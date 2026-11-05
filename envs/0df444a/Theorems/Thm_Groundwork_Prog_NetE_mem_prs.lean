-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_mem_prs
-- name    : Groundwork.Prog.NetE.mem_prs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:42.149364+00:00
-- url     : https://prove2.me/theorems/8a9e2de8-f412-4b5d-91b2-6e75c31430cf
-- title:
--   Net E: mem prs
-- statement:
--   The Net E construction uses the mem prs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L110-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L110-L112

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
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}

theorem Groundwork.Prog.NetE.mem_prs {x G G' a b : ℕ} (ha : a ∈ members K g x G) (hb : b ∈ members K g x G') :
    (a, b) ∈ prs K g x G G' := by sorry
