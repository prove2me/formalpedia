-- Prove2me | Theorems.Thm_Groundwork_Network_merge_sized
-- name    : Groundwork.Network.merge_sized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:50.206295+00:00
-- url     : https://prove2.me/theorems/366026d3-9f85-460e-9a1a-24175cf20e1c
-- title:
--   Network: merge sized
-- statement:
--   If every class has at most m members, the merged network has size P·m and values bounded by
--   2^{B·(m+m²)}:
--   a merged weight is a product of at most m weights and at most m² interactions, a merged factor or
--   interaction is a
--   product of at most m² factors or interactions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L372-L396
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L372-L396

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

theorem Groundwork.Network.merge_sized [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) {P B m : ℕ} (h : N.Sized P B) (hm : ∀ G, #{a | χ a = G} ≤ m) :
    (N.merge χ s₀ t₀).Sized (P * m) (B * (m + m * m)) := by sorry
