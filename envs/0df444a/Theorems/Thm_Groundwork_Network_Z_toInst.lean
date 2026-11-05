-- Prove2me | Theorems.Thm_Groundwork_Network_Z_toInst
-- name    : Groundwork.Network.Z_toInst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:38.189968+00:00
-- url     : https://prove2.me/theorems/5fb5637c-9d36-4787-9c88-52c6a9904277
-- title:
--   Network: Z to Inst
-- statement:
--   The instance made from a network has the network's value, for every way (D, dec) of naming its
--   labels by elements of A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L83-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L83-L109

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

theorem Groundwork.Network.Z_toInst [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] (N : Network J σ τ)
    (D : J → J → Finset A) (dec : J → J → A → τ) (h : ∀ a b, a < b → Set.BijOn (dec a b) (D a b) (N.Θ a b)) (d : A) :
    (N.toInst D dec).Z d = N.value := by sorry
