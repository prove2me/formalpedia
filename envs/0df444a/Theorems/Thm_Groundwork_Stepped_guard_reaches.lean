-- Prove2me | Theorems.Thm_Groundwork_Stepped_guard_reaches
-- name    : Groundwork.Stepped.guard_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:57.660199+00:00
-- url     : https://prove2.me/theorems/113515c4-07d2-4bcb-93b7-c5aa9a583978
-- title:
--   Stepped: guard reaches
-- statement:
--   The Stepped construction uses the guard reaches property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L36-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L36-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}

theorem Groundwork.Stepped.guard_reaches {sel : τ → Option ν} {T : Stepped ν β} {d b : β} {s : T.σ} {t S : ℕ}
    (h : T.Reaches S b s t) : (guard sel T d).Reaches (S + 1) b (some s) t := by sorry
