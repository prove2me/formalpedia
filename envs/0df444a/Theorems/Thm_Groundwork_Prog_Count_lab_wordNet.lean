-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_lab_wordNet
-- name    : Groundwork.Prog.Count.lab_wordNet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:00.799421+00:00
-- url     : https://prove2.me/theorems/433d1c4b-1936-4b7a-aba0-746ef7b59ac6
-- title:
--   Count: lab word Net
-- statement:
--   The Count construction uses the lab word Net property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L414-L420
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L414-L420

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

theorem Groundwork.Prog.Count.lab_wordNet (a b : Fin g) : (wordNet g k φ).lab a b = words (capF g k φ a.val b.val) := by sorry
