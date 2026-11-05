-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_varAt_eq_none
-- name    : Groundwork.Prog.Count.varAt_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:08.856389+00:00
-- url     : https://prove2.me/theorems/1244227f-d5a6-4461-b71a-388e67e3fe48
-- title:
--   Count: var At eq none
-- statement:
--   The Count construction uses the var At eq none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L152-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L152-L154

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}

theorem Groundwork.Prog.Count.varAt_eq_none (h0 : 0 < k) {i : ℕ} (h : φ.length * k ≤ i) : varAt k φ i = none := by sorry
