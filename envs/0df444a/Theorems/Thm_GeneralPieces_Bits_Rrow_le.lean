-- Prove2me | Theorems.Thm_GeneralPieces_Bits_Rrow_le
-- name    : GeneralPieces.Bits.Rrow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:47.511821+00:00
-- url     : https://prove2.me/theorems/79c49e68-f0c2-4a18-9a4c-923aa0edc47b
-- title:
--   Bits: Rrow le
-- statement:
--   As p is nondecreasing, R^row_s ≤ (2h+1)·p(2h+s).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L182-L185
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L182-L185

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

theorem GeneralPieces.Bits.Rrow_le (h : ℕ) (s : ℤ) : Rrow h s ≤ (2 * h + 1) * pZ (2 * h + s) := by sorry
