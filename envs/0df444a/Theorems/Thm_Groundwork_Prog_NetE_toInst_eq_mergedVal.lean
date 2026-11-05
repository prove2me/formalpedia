-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_toInst_eq_mergedVal
-- name    : Groundwork.Prog.NetE.toInst_eq_mergedVal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:00.194176+00:00
-- url     : https://prove2.me/theorems/7b2e69b0-50a4-4bef-b45c-ca8620196132
-- title:
--   Net E: to Inst eq merged Val
-- statement:
--   mergedVal is the entry of the instance of the merged network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L357-L390
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L357-L390

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

theorem Groundwork.Prog.NetE.toInst_eq_mergedVal (hK : 0 < K) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x β : ℕ) (G : Fin K) (θ : Fin K → List Bool)
    (hθ : ∀ G', G' ≠ G → (θ G').length = β) :
    (N.merge (chi hK x) [] []).toInst (mD K g Np c x β) (mdec K g Np c x) G θ =
      mergedVal K g Np N ((c, x), (G.val, List.ofFn θ)) := by sorry
