-- Prove2me | Theorems.Thm_Groundwork_Sparsify_exists_of_mem_leaves
-- name    : Groundwork.Sparsify.exists_of_mem_leaves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:00.226322+00:00
-- url     : https://prove2.me/theorems/1db91beb-4b8e-436b-833a-22ffcee82df8
-- title:
--   Sparsify: exists of mem leaves
-- statement:
--   Every listed node satisfies the invariant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L197-L215
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L197-L215

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

theorem Groundwork.Sparsify.exists_of_mem_leaves
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) : ∀ x ∈ leaves step k s, ∃ p' t', G x p' t' := by sorry
