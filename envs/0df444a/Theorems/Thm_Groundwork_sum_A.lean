-- Prove2me | Theorems.Thm_Groundwork_sum_A
-- name    : Groundwork.sum_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:04.615677+00:00
-- url     : https://prove2.me/theorems/1cf76388-4191-4624-84cf-4bd2969756c3
-- title:
--   Groundwork: sum A
-- statement:
--   Only λ+1 terms: the crossing is A_0 + … + A_λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L40-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L40-L47

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

theorem Groundwork.sum_A {n : ℕ} (x y u v : Bits n) : ∑ i ∈ range (n + 1), A n i x y u v = cross x y u v := by sorry
