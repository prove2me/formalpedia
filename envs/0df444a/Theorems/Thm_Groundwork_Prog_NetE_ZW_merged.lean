-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_ZW_merged
-- name    : Groundwork.Prog.NetE.ZW_merged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:34.519008+00:00
-- url     : https://prove2.me/theorems/fa8861d6-154b-449a-9e80-5a98847e38a9
-- title:
--   Net E: ZW merged
-- statement:
--   The value of the instance of the merged network is the value of the network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L218-L231
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L218-L231

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

theorem Groundwork.Prog.NetE.ZW_merged (hK : 0 < K) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x β : ℕ) (hβ : ∀ G G' : Fin K, G < G' → lbLen K g Np c x G G' ≤ β) :
    Inst.ZW β [] ((N.merge (chi hK x) [] []).toInst (mD K g Np c x β) (mdec K g Np c x)) = N.value := by sorry
