-- Prove2me | Theorems.Thm_Groundwork_Sparsify_length_leaves_le
-- name    : Groundwork.Sparsify.length_leaves_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:09.409531+00:00
-- url     : https://prove2.me/theorems/f219a7d4-3bde-4715-a3e3-7a94935991e6
-- title:
--   Sparsify: length leaves le
-- statement:
--   The number of leaves is at most Σ_{j ≤ h} C(d, j): d steps and h heavy steps are left.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L147-L168
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L147-L168

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

theorem Groundwork.Sparsify.length_leaves_le (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k d h : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) (hd : D ≤ p + d) (hh : T < t + (h + 1) * q) :
    (leaves step k s).length ≤ ∑ j ∈ range (h + 1), d.choose j := by sorry
