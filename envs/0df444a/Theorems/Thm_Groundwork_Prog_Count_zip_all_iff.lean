-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_zip_all_iff
-- name    : Groundwork.Prog.Count.zip_all_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:57.044048+00:00
-- url     : https://prove2.me/theorems/1cea0407-f353-41e7-ab29-4fec1662bc5f
-- title:
--   Count: zip all iff
-- statement:
--   The Count construction uses the zip all iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L285-L293
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L285-L293

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

theorem Groundwork.Prog.Count.zip_all_iff {α : Type} (u : α → Bool) : ∀ (L : List α) (θ : List Bool), θ.length = L.length →
    (((L.zip θ).all fun p => u p.1 == p.2) = true ↔ θ = L.map u)
  := by sorry
