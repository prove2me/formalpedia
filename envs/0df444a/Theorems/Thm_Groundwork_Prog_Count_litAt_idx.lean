-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_litAt_idx
-- name    : Groundwork.Prog.Count.litAt_idx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:43:41.288992+00:00
-- url     : https://prove2.me/theorems/5187dc32-7f84-42a5-ac32-55944ec610e8
-- title:
--   Count: lit At idx
-- statement:
--   The Count construction uses the lit At idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L136-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L136-L147

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

theorem Groundwork.Prog.Count.litAt_idx (p : Slot g μ k) : litAt k φ (idx p) = lit φ p := by sorry
