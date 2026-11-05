-- Prove2me | Theorems.Thm_Groundwork_cross_eq_prod
-- name    : Groundwork.cross_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:05.126186+00:00
-- url     : https://prove2.me/theorems/9ea724ee-a06f-4109-811d-bb49e83c8d74
-- title:
--   Groundwork: cross eq prod
-- statement:
--   A λ-bit crossing is the product of its bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L27-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L27-L37

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

theorem Groundwork.cross_eq_prod {n : ℕ} (x y u v : Bits n) : cross x y u v = ∏ k, X₁ (x k) (y k) (u k) (v k) := by sorry
