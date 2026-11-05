-- Prove2me | Theorems.Thm_Groundwork_uncross
-- name    : Groundwork.uncross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:00.530907+00:00
-- url     : https://prove2.me/theorems/d57937e0-ca5d-455f-a00e-7416fec819cd
-- title:
--   Groundwork: uncross
-- statement:
--   One bit of the crossing is I minus s ⊗ s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L23-L24
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L23-L24

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

theorem Groundwork.uncross (x y u v : Bool) : X₁ x y u v = I₁ x y u v - s x y * s u v := by sorry
