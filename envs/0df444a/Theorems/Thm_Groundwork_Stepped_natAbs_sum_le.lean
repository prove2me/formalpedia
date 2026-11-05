-- Prove2me | Theorems.Thm_Groundwork_Stepped_natAbs_sum_le
-- name    : Groundwork.Stepped.natAbs_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:34.878423+00:00
-- url     : https://prove2.me/theorems/244fc9cb-2e32-4085-9d85-6e1cd9808765
-- title:
--   Stepped: nat Abs sum le
-- statement:
--   The Stepped construction uses the nat Abs sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L102-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L102-L111

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

theorem Groundwork.Stepped.natAbs_sum_le (v : ℕ → ℤ) (V k : ℕ) (h : ∀ y < k, (v y).natAbs ≤ V) :
    (∑ y ∈ range k, v y).natAbs ≤ k * V := by sorry
