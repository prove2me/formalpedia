-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_length_lAt
-- name    : Groundwork.Prog.NetE.length_lAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:37.719704+00:00
-- url     : https://prove2.me/theorems/6455c049-3376-4a42-8230-a03f102bfbfd
-- title:
--   Net E: length l At
-- statement:
--   The Net E construction uses the length l At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L104-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L104-L108

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

theorem Groundwork.Prog.NetE.length_lAt {x G G' : ℕ} {θ : List Bool} {p : ℕ × ℕ} (hp : p ∈ prs K g x G G')
    (hθ : lbLen K g Np c x G G' ≤ θ.length) : (lAt K g Np c x G G' θ p).length = Np.cap c p.1 p.2 := by sorry
