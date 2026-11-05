-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_length_members
-- name    : Groundwork.Prog.NetE.length_members
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:06.688648+00:00
-- url     : https://prove2.me/theorems/a453b9ba-4a5c-454e-a964-ddd192a68b73
-- title:
--   Net E: length members
-- statement:
--   The Net E construction uses the length members property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L441-L446
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L441-L446

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
variable {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}

theorem Groundwork.Prog.NetE.length_members (hK : 0 < K) (x : ℕ) (G : Fin K) :
    (members K g x G.val).length = #{a : Fin g | chi hK x a = G} := by sorry
