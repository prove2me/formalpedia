-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_mem_links
-- name    : Groundwork.Prog.Count.mem_links
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:43:47.606533+00:00
-- url     : https://prove2.me/theorems/56d34333-493b-4ca6-9612-a2a865c1010d
-- title:
--   Count: mem links
-- statement:
--   The Count construction uses the mem links property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L215-L218
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L215-L218

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

theorem Groundwork.Prog.Count.mem_links (hg : 0 < g) (a b : ℕ) (p : ℕ × ℕ) : p ∈ links g k φ a b ↔
    p.1 < mu g φ * k ∧ p.2 < mu g φ * k ∧ linkB k φ (a * (mu g φ * k) + p.1) (b * (mu g φ * k) + p.2) = true := by sorry
