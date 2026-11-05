-- Prove2me | Theorems.Thm_Groundwork_Stepped_optBind_runs_some
-- name    : Groundwork.Stepped.optBind_runs_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:56:10.495672+00:00
-- url     : https://prove2.me/theorems/11828348-6ae9-4f61-9683-126fe065e6e8
-- title:
--   Stepped: opt Bind runs some
-- statement:
--   The Stepped construction uses the opt Bind runs some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L86-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L86-L89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}

theorem Groundwork.Stepped.optBind_runs_some [HasSize α] [HasSize β] {M : Stepped α (Option ι)} {N : Stepped (α × ι) β}
    {dflt : α → β} {a : α} {i : ι} {t t' S S' : ℕ} {b : β} (h : M.Runs a t S (some i))
    (h' : N.Runs (a, i) t' S' b) : (optBind M N dflt).Runs a (t + 1 + t') (max (size a + S) (S' + 1) + 1) b := by sorry
