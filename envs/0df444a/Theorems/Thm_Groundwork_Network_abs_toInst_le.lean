-- Prove2me | Theorems.Thm_Groundwork_Network_abs_toInst_le
-- name    : Groundwork.Network.abs_toInst_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:50.835681+00:00
-- url     : https://prove2.me/theorems/690e1114-8d32-478f-bb11-a83079d9f520
-- title:
--   Network: abs to Inst le
-- statement:
--   A value of the instance is a sum of at most 2^P terms, each a product of one weight and card J −
--   1 factors.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L400-L426
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L400-L426

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

theorem Groundwork.Network.abs_toInst_le [Fintype J] [LinearOrder J] [DecidableEq A] (N : Network J σ τ)
    (D : J → J → Finset A) (dec : J → J → A → τ) {P B : ℕ} (h : N.Sized P B) (a : J) (θ : J → A) :
    |N.toInst D dec a θ| ≤ 2 ^ (P + B * Fintype.card J) := by sorry
