-- Prove2me | Theorems.Thm_Groundwork_Colouring_card_pairs_le
-- name    : Groundwork.Colouring.card_pairs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:13.005216+00:00
-- url     : https://prove2.me/theorems/def1fb86-fd30-4f56-9e0a-211638231060
-- title:
--   Colouring: card pairs le
-- statement:
--   The fraction of colourings that send two ordered pairs from γ to γ' is at most 1/K⁴, plus 1/K²
--   for every time the pairs
--   meet.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Colouring.lean#L257-L276
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Colouring.lean#L257-L276

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

theorem Groundwork.Colouring.card_pairs_le (γ γ' : κ) (p q : ι × ι) (hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2) :
    #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')} * K ^ 4
      ≤ N + K ^ 2 * N * meet p q := by sorry
