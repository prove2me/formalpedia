-- Prove2me | Theorems.Thm_Groundwork_Stepped_foldRange_runs
-- name    : Groundwork.Stepped.foldRange_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:35.154561+00:00
-- url     : https://prove2.me/theorems/420e7f00-3a73-400d-99ae-9804c361c36d
-- title:
--   Stepped: fold Range runs
-- statement:
--   The body takes t y steps on (a, y) and returns v y. Steps of the loop: Σ_{y < N a} (t y + 1).
--   Result: the fold of g
--   over y = 0, …, N a - 1. Sc bounds the size of the accumulator, Sm the size inside the body.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L56-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L56-L82

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

theorem Groundwork.Stepped.foldRange_runs [HasSize α] [HasSize γ] {N : α → ℕ} {M : Stepped (α × ℕ) β} {g : γ → ℕ → β → γ}
    {c₀ : α → γ} {a : α} (t : ℕ → ℕ) (v : ℕ → β) (Sc Sm : ℕ) (hM : ∀ y < N a, M.Runs (a, y) (t y) Sm (v y))
    (hc : ∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) :
    (foldRange N M g c₀).Runs a (∑ y ∈ range (N a), (t y + 1)) (size a + size (N a) + (Sc + Sm) + 1)
      ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a)) := by sorry
