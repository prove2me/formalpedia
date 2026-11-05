-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_size_u_le
-- name    : Groundwork.Prog.NetE.size_u_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:34.779904+00:00
-- url     : https://prove2.me/theorems/63e91830-2115-4eaa-be74-7fb2683e0652
-- title:
--   Net E: size u le
-- statement:
--   The Net E construction uses the size u le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L260-L276
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L260-L276

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
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
variable [HasSize C]

theorem Groundwork.Prog.NetE.size_u_le (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    size ((c, x), (G.val, List.ofFn θ)) ≤ size c + size x + size K + K * (2 * β + 2) + 1 := by sorry
