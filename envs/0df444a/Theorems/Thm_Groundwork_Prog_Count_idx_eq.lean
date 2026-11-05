-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_idx_eq
-- name    : Groundwork.Prog.Count.idx_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:00.263123+00:00
-- url     : https://prove2.me/theorems/6827c7d9-2d32-47e4-a2bb-4e2acb2fb949
-- title:
--   Count: idx eq
-- statement:
--   The Count construction uses the idx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L133-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L133-L134

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

theorem Groundwork.Prog.Count.idx_eq (a : Fin g) (s : Sl μ k) : idx (a, s) = a.val * (μ * k) + loc s := by sorry
