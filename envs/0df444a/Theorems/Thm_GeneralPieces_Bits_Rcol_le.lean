-- Prove2me | Theorems.Thm_GeneralPieces_Bits_Rcol_le
-- name    : GeneralPieces.Bits.Rcol_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:51.748848+00:00
-- url     : https://prove2.me/theorems/764f77bc-89e2-411f-92f5-a0a2a2d824b8
-- title:
--   Bits: Rcol le
-- statement:
--   As p is nondecreasing, R^col_s ≤ (2h+1)·p(2h−s).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L188-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L188-L191

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

theorem GeneralPieces.Bits.Rcol_le (h : ℕ) (s : ℤ) : Rcol h s ≤ (2 * h + 1) * pZ (2 * h - s) := by sorry
