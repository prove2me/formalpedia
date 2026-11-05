-- Prove2me | Theorems.Thm_Groundwork_Sparsify_mul_card_le
-- name    : Groundwork.Sparsify.mul_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:17.134139+00:00
-- url     : https://prove2.me/theorems/ce4415f4-c970-4f0f-aa88-23b8b81e45dc
-- title:
--   Sparsify: mul card le
-- statement:
--   Double counting: i-subsets of U, each point in at most d of them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparsify.lean#L119-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparsify.lean#L119-L123

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Ring.Nat
import Definitions.Def_StepMachines_Math_Sparsify
set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]
variable {τ n : ℕ} {φ F : Finset (Finset α)} {p q : ℕ} {U : Finset α}

theorem Groundwork.Sparsify.mul_card_le (U : Finset α) (G : Finset (Finset α)) (i d : ℕ) (hU : ∀ C ∈ G, C ⊆ U)
    (hi : ∀ C ∈ G, C.card = i) (hd : ∀ a, (G.filter fun C => a ∈ C).card ≤ d) : i * G.card ≤ U.card * d := by sorry
