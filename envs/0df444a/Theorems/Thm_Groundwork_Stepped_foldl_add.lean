-- Prove2me | Theorems.Thm_Groundwork_Stepped_foldl_add
-- name    : Groundwork.Stepped.foldl_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:39.317922+00:00
-- url     : https://prove2.me/theorems/751bb416-83ac-40fa-a1c4-0009ded80016
-- title:
--   Stepped: foldl add
-- statement:
--   The Stepped construction uses the foldl add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L96-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L96-L100

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

theorem Groundwork.Stepped.foldl_add (v : ℕ → ℤ) (k : ℕ) :
    (List.range k).foldl (fun c y => c + v y) 0 = ∑ y ∈ range k, v y := by sorry
