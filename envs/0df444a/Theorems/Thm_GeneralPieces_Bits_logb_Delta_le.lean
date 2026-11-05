-- Prove2me | Theorems.Thm_GeneralPieces_Bits_logb_Delta_le
-- name    : GeneralPieces.Bits.logb_Delta_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:01.094257+00:00
-- url     : https://prove2.me/theorems/04d2eab0-555f-4489-b563-b86bf467d017
-- title:
--   Bits: logb Delta le
-- statement:
--   By display (46): log Δ ≤ 2κ√h + log(4h+1) + C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L276-L285
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L276-L285

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}

theorem GeneralPieces.Bits.logb_Delta_le (hB : Bounds B C) (h : ℕ) : logb 2 (Delta h) ≤ 2 * (kappa * √(h : ℝ)) + logb 2 (4 * (h : ℝ) + 1) + C := by sorry
