-- Prove2me | Theorems.Thm_Groundwork_abs_prod_le_two_pow
-- name    : Groundwork.abs_prod_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:53.758669+00:00
-- url     : https://prove2.me/theorems/1edbd9d3-4495-4d03-8eb5-1d3d91a7cd9f
-- title:
--   Groundwork: abs prod le two pow
-- statement:
--   A product of at most k integers of absolute value at most 2^B has absolute value at most
--   2^(B·k).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L48-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L48-L53

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

theorem Groundwork.abs_prod_le_two_pow {ι : Type*} (s : Finset ι) (f : ι → ℤ) {B k : ℕ} (h : ∀ i ∈ s, |f i| ≤ 2 ^ B)
    (hk : #s ≤ k) : |∏ i ∈ s, f i| ≤ 2 ^ (B * k) := by sorry
