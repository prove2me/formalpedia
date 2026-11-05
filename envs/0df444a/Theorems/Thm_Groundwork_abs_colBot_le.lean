-- Prove2me | Theorems.Thm_Groundwork_abs_colBot_le
-- name    : Groundwork.abs_colBot_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:43.479755+00:00
-- url     : https://prove2.me/theorems/013861d6-fd44-4f78-a5d0-bca4cda5050c
-- title:
--   Groundwork: abs col Bot le
-- statement:
--   Across columns, the factors on the second side of the cut have absolute value at most 2^λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L179-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L179-L182

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

theorem Groundwork.abs_colBot_le {n : ℕ} (i : ℕ) (β : Fin n → Bell) (p q : Bits n) : |colBit.Bot i β p q| ≤ 2 ^ n := by sorry
