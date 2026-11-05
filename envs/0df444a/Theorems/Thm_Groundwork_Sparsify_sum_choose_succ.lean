-- Prove2me | Theorems.Thm_Groundwork_Sparsify_sum_choose_succ
-- name    : Groundwork.Sparsify.sum_choose_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:46.438773+00:00
-- url     : https://prove2.me/theorems/ba7753c5-232b-4018-9894-995ed7fd4560
-- title:
--   Sparsify: sum choose succ
-- statement:
--   The Sparsify construction uses the sum choose succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L135-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L135-L140

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

theorem Groundwork.Sparsify.sum_choose_succ (d h : ℕ) :
    ∑ j ∈ range (h + 1 + 1), (d + 1).choose j =
      ∑ j ∈ range (h + 1 + 1), d.choose j + ∑ j ∈ range (h + 1), d.choose j := by sorry
