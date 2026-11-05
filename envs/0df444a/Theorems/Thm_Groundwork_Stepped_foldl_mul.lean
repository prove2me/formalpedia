-- Prove2me | Theorems.Thm_Groundwork_Stepped_foldl_mul
-- name    : Groundwork.Stepped.foldl_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:53.857326+00:00
-- url     : https://prove2.me/theorems/51ba525c-91d5-4efd-8c8c-efeb345c4b3b
-- title:
--   Stepped: foldl mul
-- statement:
--   The Stepped construction uses the foldl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L137-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L137-L141

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range
import Definitions.Def_StepMachines_Prog_Range
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Finset
variable {α β γ : Type}

theorem Groundwork.Stepped.foldl_mul (v : ℕ → ℤ) (k : ℕ) :
    (List.range k).foldl (fun c y => c * v y) 1 = ∏ y ∈ range k, v y := by sorry
