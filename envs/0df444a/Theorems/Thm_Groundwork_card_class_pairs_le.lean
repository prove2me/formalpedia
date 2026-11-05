-- Prove2me | Theorems.Thm_Groundwork_card_class_pairs_le
-- name    : Groundwork.card_class_pairs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:35.60974+00:00
-- url     : https://prove2.me/theorems/392edd92-928e-4c84-b449-579ee353f5f1
-- title:
--   Groundwork: card class pairs le
-- statement:
--   If every class has at most m members, there are at most m² ordered pairs from one class to
--   another.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L57-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L57-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}

theorem Groundwork.card_class_pairs_le [Fintype J] [DecidableEq J'] (χ : J → J') {m : ℕ} (hm : ∀ G, #{a | χ a = G} ≤ m)
    (G G' : J') : #{p : J × J | χ p.1 = G ∧ χ p.2 = G'} ≤ m * m := by sorry
