-- Prove2me | Theorems.Thm_Groundwork_Stepped_sumRange_runs
-- name    : Groundwork.Stepped.sumRange_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:27:42.359518+00:00
-- url     : https://prove2.me/theorems/79600c76-a4ff-47a6-b2f7-71db552c9f09
-- title:
--   Stepped: sum Range runs
-- statement:
--   Steps: Σ_{y < N a} (t y + 1). Result: Σ_{y < N a} v y. V bounds every |v y|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L114-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L114-L123

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

theorem Groundwork.Stepped.sumRange_runs [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) ℤ} {a : α} (t : ℕ → ℕ) (v : ℕ → ℤ)
    (V Sm : ℕ) (hM : ∀ y < N a, M.Runs (a, y) (t y) Sm (v y)) (hV : ∀ y < N a, (v y).natAbs ≤ V) :
    (sumRange N M).Runs a (∑ y ∈ range (N a), (t y + 1)) (size a + size (N a) + (size (N a * V) + Sm) + 1)
      (∑ y ∈ range (N a), v y) := by sorry
