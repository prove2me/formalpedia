-- Prove2me | Theorems.Thm_Groundwork_Prog_capF_le
-- name    : Groundwork.Prog.capF_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:37.96137+00:00
-- url     : https://prove2.me/theorems/8c63d4a7-8f67-4006-8d6e-697b6d5f019f
-- title:
--   Prog: cap F le
-- statement:
--   The Prog construction uses the cap F le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Count.lean#L60-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Count.lean#L60-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatArith
import Definitions.Def_StepMachines_Prog_Count
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset Groundwork.Prog.Count

theorem Groundwork.Prog.capF_le {g k : ℕ} (hg : 0 < g) (φ : Fml) {a b : Fin g} (hab : a ≠ b) :
    capF g k φ a.val b.val ≤ 2 * (mu g φ * k) := by sorry
