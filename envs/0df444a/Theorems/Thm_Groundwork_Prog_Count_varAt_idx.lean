-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_varAt_idx
-- name    : Groundwork.Prog.Count.varAt_idx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:05.438944+00:00
-- url     : https://prove2.me/theorems/20a4adc9-ba64-4d3b-9555-7de3afe2087a
-- title:
--   Count: var At idx
-- statement:
--   The Count construction uses the var At idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L149-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L149-L150

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

theorem Groundwork.Prog.Count.varAt_idx (p : Slot g μ k) : varAt k φ (idx p) = lab φ p := by sorry
