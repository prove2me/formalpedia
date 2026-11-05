-- Prove2me | Theorems.Thm_Groundwork_Network_merge_summand
-- name    : Groundwork.Network.merge_summand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:54.957193+00:00
-- url     : https://prove2.me/theorems/157e49b0-996b-41ff-b1c5-7308f9ee8b2e
-- title:
--   Network: merge summand
-- statement:
--   One summand of the value of a network, regrouped by classes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L243-L286
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L243-L286

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

theorem Groundwork.Network.merge_summand [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) (z : J → σ) :
    (∏ a, N.W a (z a)) * ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2) =
    (∏ G, (N.merge χ s₀ t₀).W G (fun a => if χ a = G then z a else s₀)) *
      ∏ q ∈ pairs J', (N.merge χ s₀ t₀).Ψ q.1 q.2 (fun a => if χ a = q.1 then z a else s₀)
        (fun a => if χ a = q.2 then z a else s₀) := by sorry
