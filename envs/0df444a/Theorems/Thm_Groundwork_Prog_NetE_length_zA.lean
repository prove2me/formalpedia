-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_length_zA
-- name    : Groundwork.Prog.NetE.length_zA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:34.428192+00:00
-- url     : https://prove2.me/theorems/a90c6021-39d0-419d-8766-0973bf2fb0d0
-- title:
--   Net E: length z A
-- statement:
--   The Net E construction uses the length z A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L98-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L98-L102

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

theorem Groundwork.Prog.NetE.length_zA {x G : ℕ} {θs : List (List Bool)} {y a : ℕ} (ha : a ∈ members K g x G) :
    (zA K g Np (((c, x), (G, θs)), y) a).length = Np.n c a := by sorry
