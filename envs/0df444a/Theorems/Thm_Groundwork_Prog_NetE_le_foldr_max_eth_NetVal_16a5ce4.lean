-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_le_foldr_max_eth_NetVal_16a5ce4
-- name    : Groundwork.Prog.NetE.le_foldr_max_eth_NetVal_16a5ce4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:07.61813+00:00
-- url     : https://prove2.me/theorems/022e4932-3ac7-49a3-b3a1-c095c25d1702
-- title:
--   Net E: le foldr max eth Net Val 16a5ce4
-- statement:
--   The Net E construction uses the le foldr max eth Net Val 16a5ce4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L402-L408
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L402-L408

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

theorem Groundwork.Prog.NetE.le_foldr_max_eth_NetVal_16a5ce4 {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by sorry
