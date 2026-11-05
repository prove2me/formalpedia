-- Prove2me | Theorems.Thm_Groundwork_Network_merge_shaped
-- name    : Groundwork.Network.merge_shaped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:48.436581+00:00
-- url     : https://prove2.me/theorems/cfa20f38-f546-435e-8baf-674e1ab78844
-- title:
--   Network: merge shaped
-- statement:
--   If every class has at most m members, the merged network has the shape of a network of size P·m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L320-L365
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L320-L365

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

theorem Groundwork.Network.merge_shaped [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) {P m : ℕ} (h : N.Shaped P) (hm : ∀ G, #{a | χ a = G} ≤ m) :
    (N.merge χ s₀ t₀).Shaped (P * m) := by sorry
