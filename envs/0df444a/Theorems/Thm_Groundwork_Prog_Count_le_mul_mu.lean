-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_le_mul_mu
-- name    : Groundwork.Prog.Count.le_mul_mu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:30.793366+00:00
-- url     : https://prove2.me/theorems/2e60eb6e-b39a-4399-8229-ffa1286a1730
-- title:
--   Count: le mul mu
-- statement:
--   The Count construction uses the le mul mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L398-L398
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L398-L398

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

theorem Groundwork.Prog.Count.le_mul_mu {g : ℕ} (hg : 0 < g) (φ : Fml) : φ.length ≤ g * mu g φ := by sorry
