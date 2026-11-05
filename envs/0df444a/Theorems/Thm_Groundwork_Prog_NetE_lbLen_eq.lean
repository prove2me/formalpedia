-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_lbLen_eq
-- name    : Groundwork.Prog.NetE.lbLen_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:00.140348+00:00
-- url     : https://prove2.me/theorems/554f12d1-0c8f-48d0-908a-960e2e68967c
-- title:
--   Net E: lb Len eq
-- statement:
--   The Net E construction uses the lb Len eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L448-L458
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L448-L458

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

theorem Groundwork.Prog.NetE.lbLen_eq (hK : 0 < K) (hN : Np.Presents c N t S) (x : ℕ) {G G' : Fin K} (hne : G ≠ G') :
    lbLen K g Np c x G.val G'.val = (N.merge (chi hK x) [] []).c G G' := by sorry
