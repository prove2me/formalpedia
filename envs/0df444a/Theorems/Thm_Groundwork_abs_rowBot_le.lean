-- Prove2me | Theorems.Thm_Groundwork_abs_rowBot_le
-- name    : Groundwork.abs_rowBot_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:39.994759+00:00
-- url     : https://prove2.me/theorems/d3bfb4ab-114f-48f9-9213-8712ec814d0a
-- title:
--   Groundwork: abs row Bot le
-- statement:
--   Across rows, the factors on the second side of the cut have absolute value at most 2^λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L173-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L173-L176

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts
set_option autoImplicit false
section
section
open Groundwork
open Finset

theorem Groundwork.abs_rowBot_le {n : ℕ} (i : ℕ) (β : Fin n → Bell) (p q : Bits n) : |rowBit.Bot i β p q| ≤ 2 ^ n := by sorry
