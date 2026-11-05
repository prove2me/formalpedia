-- Prove2me | Theorems.Thm_Groundwork_Stepped_both_reaches_inr
-- name    : Groundwork.Stepped.both_reaches_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:58.756649+00:00
-- url     : https://prove2.me/theorems/b87c429a-3fa4-4f8e-a89f-55d7ee0ecc59
-- title:
--   Stepped: both reaches inr
-- statement:
--   The Stepped construction uses the both reaches inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L104-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L104-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}

theorem Groundwork.Stepped.both_reaches_inr [HasSize α] [HasSize β] {M : Stepped α β} {N : Stepped α γ} {S t : ℕ} {b : β} {c : γ}
    {s : N.σ} (h : N.Reaches S c s t) : (both M N).Reaches (size b + S + 1) (b, c) (.inr (b, s)) t := by sorry
