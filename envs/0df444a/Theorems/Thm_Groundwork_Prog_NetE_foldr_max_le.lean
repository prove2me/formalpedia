-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_foldr_max_le
-- name    : Groundwork.Prog.NetE.foldr_max_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:59.769817+00:00
-- url     : https://prove2.me/theorems/045d63c5-2d94-4ee8-9072-8b5f7dc4ff02
-- title:
--   Net E: foldr max le
-- statement:
--   The Net E construction uses the foldr max le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L410-L414
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L410-L414

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

theorem Groundwork.Prog.NetE.foldr_max_le {l : List ℕ} {P : ℕ} (h : ∀ x ∈ l, x ≤ P) : l.foldr max 0 ≤ P := by sorry
