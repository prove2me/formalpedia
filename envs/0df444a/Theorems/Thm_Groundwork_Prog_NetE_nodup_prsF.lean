-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_nodup_prsF
-- name    : Groundwork.Prog.NetE.nodup_prsF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:16.667659+00:00
-- url     : https://prove2.me/theorems/aed1f078-8e1b-4760-9a93-2294c35111bd
-- title:
--   Net E: nodup prs F
-- statement:
--   The Net E construction uses the nodup prs F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L134-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L134-L136

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

theorem Groundwork.Prog.NetE.nodup_prsF (x G G' : ℕ) : (prsF K x G G' : List (Fin g × Fin g)).Nodup := by sorry
