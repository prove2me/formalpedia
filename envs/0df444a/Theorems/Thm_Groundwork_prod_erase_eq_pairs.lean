-- Prove2me | Theorems.Thm_Groundwork_prod_erase_eq_pairs
-- name    : Groundwork.prod_erase_eq_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:51.587636+00:00
-- url     : https://prove2.me/theorems/9bfbdf57-fbee-4b44-ab7b-a4640faa8066
-- title:
--   Groundwork: prod erase eq pairs
-- statement:
--   A product over ordered pairs of distinct nodes, regrouped by unordered pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L25-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L25-L35

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

theorem Groundwork.prod_erase_eq_pairs [Fintype J] [LinearOrder J] (G : J → J → ℤ) :
    ∏ a, ∏ b ∈ univ.erase a, G a b = ∏ p ∈ pairs J, G p.1 p.2 * G p.2 p.1 := by sorry
