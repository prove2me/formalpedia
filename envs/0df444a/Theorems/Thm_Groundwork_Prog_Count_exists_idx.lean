-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_exists_idx
-- name    : Groundwork.Prog.Count.exists_idx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:10.307141+00:00
-- url     : https://prove2.me/theorems/f2c889cc-ab9b-47a4-98c4-6b0b2cf4eacc
-- title:
--   Count: exists idx
-- statement:
--   The Count construction uses the exists idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L156-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L156-L165

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

theorem Groundwork.Prog.Count.exists_idx {i : ℕ} (h : i < g * μ * k) : ∃ p : Slot g μ k, idx p = i := by sorry
