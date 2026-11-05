-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_nodup_links
-- name    : Groundwork.Prog.Count.nodup_links
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:12.603273+00:00
-- url     : https://prove2.me/theorems/388967d3-84ab-4737-aeaa-8eeea40738d1
-- title:
--   Count: nodup links
-- statement:
--   The Count construction uses the nodup links property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L220-L222
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L220-L222

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

theorem Groundwork.Prog.Count.nodup_links (hg : 0 < g) (a b : ℕ) : (links g k φ a b).Nodup := by sorry
