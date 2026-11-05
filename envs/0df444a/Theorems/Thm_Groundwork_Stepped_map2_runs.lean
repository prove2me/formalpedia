-- Prove2me | Theorems.Thm_Groundwork_Stepped_map2_runs
-- name    : Groundwork.Stepped.map2_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:12.783483+00:00
-- url     : https://prove2.me/theorems/389d1214-96f7-44ab-81d6-9c43fad02a8d
-- title:
--   Stepped: map2 runs
-- statement:
--   The Stepped construction uses the map2 runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L140-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L140-L143

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}

theorem Groundwork.Stepped.map2_runs [HasSize α] [HasSize β] {f : β → γ → δ} {M : Stepped α β} {N : Stepped α γ} {a : α}
    {t t' S S' : ℕ} {b : β} {c : γ} (h : M.Runs a t S b) (h' : N.Runs a t' S' c) :
    (map2 f M N).Runs a (t + 1 + t') (max (size a + S) (size b + S') + 1) (f b c) := by sorry
