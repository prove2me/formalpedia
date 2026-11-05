-- Prove2me | Theorems.Thm_GeneralPieces_Bits_bounds_abs
-- name    : GeneralPieces.Bits.bounds_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:57.143482+00:00
-- url     : https://prove2.me/theorems/594260c7-1154-4419-8840-e586eb4b1c55
-- title:
--   Bits: bounds abs
-- statement:
--   Display (46) with B holds with |B| as well, because log E ≥ 0 for E ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L42-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L42-L47

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

theorem GeneralPieces.Bits.bounds_abs (hB : Bounds B C) : Bounds |B| C := by sorry
