-- Prove2me | Theorems.Thm_Groundwork_abs_colTop_le
-- name    : Groundwork.abs_colTop_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:41.330123+00:00
-- url     : https://prove2.me/theorems/4ddcd0b1-8509-4c78-bfde-fffc9d35258b
-- title:
--   Groundwork: abs col Top le
-- statement:
--   Across columns, the factors on the first side of the cut are 0 or ±1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L168-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L168-L170

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

theorem Groundwork.abs_colTop_le {n : ℕ} (β : Fin n → Bell) (p q : Bits n) : |colBit.Top β p q| ≤ 1 := by sorry
