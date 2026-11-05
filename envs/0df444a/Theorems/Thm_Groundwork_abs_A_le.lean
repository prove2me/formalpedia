-- Prove2me | Theorems.Thm_Groundwork_abs_A_le
-- name    : Groundwork.abs_A_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:05.699221+00:00
-- url     : https://prove2.me/theorems/a7d49017-e519-4d95-959d-fe959cfd2335
-- title:
--   Groundwork: abs A le
-- statement:
--   At most C(λ,i) ≤ 2^λ terms, each 0 or ±1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L69-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L69-L72

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

theorem Groundwork.abs_A_le (n i : ℕ) (x y u v : Bits n) : |A n i x y u v| ≤ 2 ^ n := by sorry
