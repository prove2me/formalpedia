-- Prove2me | Theorems.Thm_Groundwork_Stepped_mul2_runs
-- name    : Groundwork.Stepped.mul2_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:56:07.868891+00:00
-- url     : https://prove2.me/theorems/508935cc-bcbf-406f-be3d-135989918a0c
-- title:
--   Stepped: mul2 runs
-- statement:
--   The Stepped construction uses the mul2 runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L148-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L148-L151

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}

theorem Groundwork.Stepped.mul2_runs [HasSize α] {M N : Stepped α ℤ} {a : α} {t t' S S' : ℕ} {b c : ℤ}
    (h : M.Runs a t S b) (h' : N.Runs a t' S' c) :
    (mul2 M N).Runs a (t + 1 + t') (max (size a + S) (size b + S') + 1) (b * c) := by sorry
