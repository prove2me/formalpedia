-- Prove2me | Theorems.Thm_Groundwork_Sparsify_step_eq_none_of_mem_leaves
-- name    : Groundwork.Sparsify.step_eq_none_of_mem_leaves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:32.054107+00:00
-- url     : https://prove2.me/theorems/ea0c8fbb-cb29-4846-a51d-95230e9a3f1b
-- title:
--   Sparsify: step eq none of mem leaves
-- statement:
--   If k ≥ D − p the cut at depth k removes nothing: the list holds true leaves only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L171-L194
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L171-L194

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

theorem Groundwork.Sparsify.step_eq_none_of_mem_leaves (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) (hk : D ≤ p + k) : ∀ x ∈ leaves step k s, step x = none := by sorry
