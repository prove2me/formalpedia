-- Prove2me | Theorems.Thm_GeneralPieces_Bits_bits_le
-- name    : GeneralPieces.Bits.bits_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:00.866071+00:00
-- url     : https://prove2.me/theorems/50b59268-67cb-4013-a038-f8bdc5b95121
-- title:
--   Bits: bits le
-- statement:
--   The display, first inequality: c^row_s + c^col_s ≤ 2√2·κ√h + 2·log(2h+1) + 2C + 2, for |s| ≤ 2h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L219-L240
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L219-L240

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

theorem GeneralPieces.Bits.bits_le (hB : Bounds B C) {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) :
    ((Nat.clog 2 (Rrow h s) + Nat.clog 2 (Rcol h s) : ℕ) : ℝ) ≤ 2 * √2 * (kappa * √(h : ℝ)) + 2 * logb 2 (2 * (h : ℝ) + 1) + 2 * C + 2 := by sorry
