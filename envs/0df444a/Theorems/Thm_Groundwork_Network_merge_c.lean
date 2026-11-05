-- Prove2me | Theorems.Thm_Groundwork_Network_merge_c
-- name    : Groundwork.Network.merge_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:56:56.074093+00:00
-- url     : https://prove2.me/theorems/85474438-f334-4a42-b76d-b52b24e19c54
-- title:
--   Network: merge c
-- statement:
--   The capacity between two classes of the merged network, as an iterated sum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/ColouringNet.lean#L21-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/ColouringNet.lean#L21-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_ColouringNet
set_option autoImplicit false
section
open Groundwork Groundwork.Network
open Finset
variable {J J' σ τ : Type*}

theorem Groundwork.Network.merge_c [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ)
    (t₀ : τ) (G G' : J') :
    (N.merge χ s₀ t₀).c G G' = ∑ a with χ a = G, ∑ b with χ b = G', N.c a b := by sorry
