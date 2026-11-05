-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_linkB_iff
-- name    : Groundwork.Prog.Count.linkB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:24:25.080925+00:00
-- url     : https://prove2.me/theorems/19f3dabb-8414-4ed6-bd4e-aff797de3258
-- title:
--   Count: link B iff
-- statement:
--   The Count construction uses the link B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L167-L187
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L167-L187

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

theorem Groundwork.Prog.Count.linkB_iff (hm : φ.length ≤ g * μ) (p q : Slot g μ k) : linkB k φ (idx p) (idx q) = true ↔ Link φ p q := by sorry
