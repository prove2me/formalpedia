-- Prove2me | Theorems.Thm_Groundwork_abs_prod_le_one
-- name    : Groundwork.abs_prod_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:15.122379+00:00
-- url     : https://prove2.me/theorems/1fd9173f-3d4f-4ac7-9f38-115324da8e3b
-- title:
--   Groundwork: abs prod le one
-- statement:
--   A product of integers of absolute value at most 1 has absolute value at most 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L50-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L50-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Groundwork_Cross_Bit
set_option autoImplicit false
section
section
open Groundwork
open Finset

theorem Groundwork.abs_prod_le_one {ι : Type} (S : Finset ι) (f : ι → ℤ) (h : ∀ k, |f k| ≤ 1) : |∏ k ∈ S, f k| ≤ 1 := by sorry
