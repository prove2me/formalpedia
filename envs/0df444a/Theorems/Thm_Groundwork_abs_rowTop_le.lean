-- Prove2me | Theorems.Thm_Groundwork_abs_rowTop_le
-- name    : Groundwork.abs_rowTop_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:36.833088+00:00
-- url     : https://prove2.me/theorems/ba884090-ea55-4061-8cc5-4d4cea4af0d2
-- title:
--   Groundwork: abs row Top le
-- statement:
--   Across rows, the factors on the first side of the cut are 0 or ±1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L163-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L163-L165

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

theorem Groundwork.abs_rowTop_le {n : ℕ} (β : Fin n → Bell) (p q : Bits n) : |rowBit.Top β p q| ≤ 1 := by sorry
