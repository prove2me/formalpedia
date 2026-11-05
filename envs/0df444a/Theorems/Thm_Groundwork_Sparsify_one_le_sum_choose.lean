-- Prove2me | Theorems.Thm_Groundwork_Sparsify_one_le_sum_choose
-- name    : Groundwork.Sparsify.one_le_sum_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:48.361686+00:00
-- url     : https://prove2.me/theorems/ace9f614-3813-44c7-85fe-bb592ded74de
-- title:
--   Sparsify: one le sum choose
-- statement:
--   The Sparsify construction uses the one le sum choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L142-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L142-L144

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Definitions.Def_StepMachines_Math_SparsifyTree
set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))
variable {step} {G : σ → ℕ → ℕ → Prop} {D T q : ℕ}

theorem Groundwork.Sparsify.one_le_sum_choose (d h : ℕ) : 1 ≤ ∑ j ∈ range (h + 1), d.choose j := by sorry
