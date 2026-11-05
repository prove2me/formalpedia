-- Prove2me | Theorems.Thm_Groundwork_Sparsify_iff_exists_mem_leaves
-- name    : Groundwork.Sparsify.iff_exists_mem_leaves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:47.354197+00:00
-- url     : https://prove2.me/theorems/d0dd940a-eb5c-4e32-9c8d-b959026683c9
-- title:
--   Sparsify: iff exists mem leaves
-- statement:
--   If a property holds at a node exactly when it holds at one of the node's two children, then it
--   holds at s exactly when it holds at one of the leaves below s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L219-L232
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L219-L232

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

theorem Groundwork.Sparsify.iff_exists_mem_leaves
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (S : σ → Prop) (hS : ∀ s p t l h, G s p t → step s = some (l, h) → (S s ↔ S l ∨ S h))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) : S s ↔ ∃ x ∈ leaves step k s, S x := by sorry
