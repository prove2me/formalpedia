-- Prove2me | Theorems.Thm_Groundwork_Colouring_exists_colouring_beta
-- name    : Groundwork.Colouring.exists_colouring_beta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:18.326233+00:00
-- url     : https://prove2.me/theorems/154dc43e-5bbe-4fa5-9ac7-1d7113b8d447
-- title:
--   Colouring: exists colouring beta
-- statement:
--   The colouring lemma with β: small classes, every class-pair capacity at most β.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Colouring.lean#L505-L512
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Colouring.lean#L505-L512

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

theorem Groundwork.Colouring.exists_colouring_beta {K g : ℕ} (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g)
    (c : Fin g → Fin g → ℕ) (hs : ∀ a b, c a b = c b a) (P : ℕ)
    (hP : ∀ a, ∑ b with b ≠ a, c a b ≤ P) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
        ≤ beta K g (∑ a, ∑ b with b ≠ a, c a b) P := by sorry
