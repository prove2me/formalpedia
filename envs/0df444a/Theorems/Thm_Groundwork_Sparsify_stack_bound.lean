-- Prove2me | Theorems.Thm_Groundwork_Sparsify_stack_bound
-- name    : Groundwork.Sparsify.stack_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:09.961107+00:00
-- url     : https://prove2.me/theorems/5f04e04d-f918-4b95-9ebb-b30a28afdefc
-- title:
--   Sparsify: stack bound
-- statement:
--   At all times the stack holds at most D + 1 nodes, and each satisfies the invariant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L263-L278
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L263-L278

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

theorem Groundwork.Sparsify.stack_bound (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (s : σ) (p t : ℕ) (hG : G s p t) (i : ℕ) :
    ((round step)^[i] ([s], [])).1.length ≤ D + 1 ∧ ∀ x ∈ ((round step)^[i] ([s], [])).1, ∃ p' t', G x p' t' := by sorry
