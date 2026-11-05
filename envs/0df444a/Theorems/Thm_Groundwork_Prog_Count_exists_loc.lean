-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_exists_loc
-- name    : Groundwork.Prog.Count.exists_loc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:21.919718+00:00
-- url     : https://prove2.me/theorems/ab398063-6e93-4f9b-b921-19906e1ece2a
-- title:
--   Count: exists loc
-- statement:
--   The Count construction uses the exists loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L126-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L126-L131

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

theorem Groundwork.Prog.Count.exists_loc {r : ℕ} (h : r < μ * k) : ∃ s : Sl μ k, loc s = r := by sorry
