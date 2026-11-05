-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_labOf_eq_mdec
-- name    : Groundwork.Prog.NetE.labOf_eq_mdec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:14.589636+00:00
-- url     : https://prove2.me/theorems/bc134927-3245-4939-8376-bf0db025a655
-- title:
--   Net E: lab Of eq mdec
-- statement:
--   The Net E construction uses the lab Of eq mdec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L264-L275
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L264-L275

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

theorem Groundwork.Prog.NetE.labOf_eq_mdec (hK : 0 < K) (c : C) (x : ℕ) (G G' : Fin K) (hne : G' ≠ G) (θ : Fin K → List Bool)
    (p : Fin g × Fin g) (hp : chi hK x p.2 = G') :
    labOf K g Np ((c, x), (G.val, List.ofFn θ)) p.1 p.2 =
      mdec K g Np c x (min G G') (max G G') (θ G') (if G < G' then p else p.swap) := by sorry
