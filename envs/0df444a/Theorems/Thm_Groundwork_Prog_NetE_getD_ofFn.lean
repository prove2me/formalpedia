-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_getD_ofFn
-- name    : Groundwork.Prog.NetE.getD_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:26.611519+00:00
-- url     : https://prove2.me/theorems/0e87077e-50cb-40e5-aeb5-a6164f5022f6
-- title:
--   Net E: get D of Fn
-- statement:
--   The Net E construction uses the get D of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L239-L240
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L239-L240

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

theorem Groundwork.Prog.NetE.getD_ofFn (θ : Fin K → List Bool) (G : Fin K) : (List.ofFn θ).getD G.val [] = θ G := by sorry
