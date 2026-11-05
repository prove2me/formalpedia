-- Prove2me | Theorems.Thm_Groundwork_Stepped_firstRange_runs
-- name    : Groundwork.Stepped.firstRange_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:04.055143+00:00
-- url     : https://prove2.me/theorems/3c866c59-9975-4f4f-bd7a-d2caa6b8f86d
-- title:
--   Stepped: first Range runs
-- statement:
--   Steps: Σ_{y < N a} (t y + 1); the loop does not stop early. Result: the least y < N a such that
--   p holds of v y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L191-L204
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L191-L204

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

theorem Groundwork.Stepped.firstRange_runs [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) β} {p : β → Bool} {a : α}
    (t : ℕ → ℕ) (v : ℕ → β) (Sm : ℕ) (hM : ∀ y < N a, M.Runs (a, y) (t y) Sm (v y)) :
    (firstRange N M p).Runs a (∑ y ∈ range (N a), (t y + 1))
      (size a + size (N a) + (size (N a) + 1 + Sm) + 1) ((List.range (N a)).find? fun y => p (v y)) := by sorry
