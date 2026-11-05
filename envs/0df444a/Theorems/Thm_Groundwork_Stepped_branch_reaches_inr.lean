-- Prove2me | Theorems.Thm_Groundwork_Stepped_branch_reaches_inr
-- name    : Groundwork.Stepped.branch_reaches_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:59.718872+00:00
-- url     : https://prove2.me/theorems/e48e993b-78ea-49f4-8323-491b17eabc5d
-- title:
--   Stepped: branch reaches inr
-- statement:
--   The Stepped construction uses the branch reaches inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L33-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L33-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}

theorem Groundwork.Stepped.branch_reaches_inr {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} {S t : ℕ} {b : β}
    {s : M₂.σ} (h : M₂.Reaches S b s t) : (branch sel M₁ M₂).Reaches (S + 1) b (.inr s) t := by sorry
