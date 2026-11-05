-- Prove2me | Theorems.Thm_GeneralPieces_Bits_sqrt_add_sqrt_le
-- name    : GeneralPieces.Bits.sqrt_add_sqrt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:16.464421+00:00
-- url     : https://prove2.me/theorems/19812f0c-6343-4c7f-85ee-4da4582f2c05
-- title:
--   Bits: sqrt add sqrt le
-- statement:
--   √(2h+s) + √(2h−s) ≤ 2√(2h), for |s| ≤ 2h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L194-L205
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L194-L205

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

theorem GeneralPieces.Bits.sqrt_add_sqrt_le {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) : √(2 * (h : ℝ) + s) + √(2 * (h : ℝ) - s) ≤ 2 * √(2 * (h : ℝ)) := by sorry
