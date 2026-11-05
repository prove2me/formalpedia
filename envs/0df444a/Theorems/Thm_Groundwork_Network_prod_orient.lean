-- Prove2me | Theorems.Thm_Groundwork_Network_prod_orient
-- name    : Groundwork.Network.prod_orient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:54.208298+00:00
-- url     : https://prove2.me/theorems/f78b74c8-b743-4ab3-a819-f9318fdde172
-- title:
--   Network: prod orient
-- statement:
--   A product of a symmetric function over unordered pairs in different classes, oriented by class
--   or by node.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L219-L240
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L219-L240

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

theorem Groundwork.Network.prod_orient [Fintype J] [LinearOrder J] [LinearOrder J'] (χ : J → J') (F : J × J → ℤ) (hF : ∀ p, F p.swap = F p) :
    ∏ p : J × J with χ p.1 < χ p.2, F p = ∏ p ∈ pairs J with χ p.1 ≠ χ p.2, F p := by sorry
