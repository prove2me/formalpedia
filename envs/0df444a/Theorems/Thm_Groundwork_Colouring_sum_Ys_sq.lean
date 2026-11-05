-- Prove2me | Theorems.Thm_Groundwork_Colouring_sum_Ys_sq
-- name    : Groundwork.Colouring.sum_Ys_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:56:25.146837+00:00
-- url     : https://prove2.me/theorems/31af750d-20cc-4f79-b4c8-54a03c54b7db
-- title:
--   Colouring: sum Ys sq
-- statement:
--   Second moment of the capacity between two classes: at most (U/K²)² + 4PU/K².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Colouring.lean#L297-L345
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Colouring.lean#L297-L345

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Floor.Semifield
import Definitions.Def_Groundwork_Net_Colouring
set_option autoImplicit false
section
open Finset
open Groundwork Groundwork.Colouring
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι
local notation "N" => (Fintype.card κ ^ Fintype.card ι)
variable (c : ι → ι → ℕ)

theorem Groundwork.Colouring.sum_Ys_sq (hd : ∀ a, c a a = 0) (hs : ∀ a b, c a b = c b a) (P : ℕ)
    (hP : ∀ a, ∑ b, c a b ≤ P) (γ γ' : κ) :
    (∑ χ : ι → κ, Ys c γ γ' χ ^ 2) * K ^ 4 ≤ N * Us c ^ 2 + 4 * K ^ 2 * N * P * Us c := by sorry
