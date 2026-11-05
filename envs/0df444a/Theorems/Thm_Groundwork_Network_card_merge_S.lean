-- Prove2me | Theorems.Thm_Groundwork_Network_card_merge_S
-- name    : Groundwork.Network.card_merge_S
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:08.22466+00:00
-- url     : https://prove2.me/theorems/30ddb2ce-a4d2-4aa5-88db-645b868e5d91
-- title:
--   Network: card merge S
-- statement:
--   The number of states of a class.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L315-L317
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L315-L317

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
open Groundwork.Network

theorem Groundwork.Network.card_merge_S [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    (G : J') : #((N.merge χ s₀ t₀).S G) = ∏ a with χ a = G, #(N.S a) := by sorry
