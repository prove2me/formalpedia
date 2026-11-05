-- Prove2me | Theorems.Thm_GeneralPieces_Bits_pZ_mono
-- name    : GeneralPieces.Bits.pZ_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:41.397473+00:00
-- url     : https://prove2.me/theorems/5b15f875-f927-4eb5-b933-5a373fe91927
-- title:
--   Bits: p Z mono
-- statement:
--   p is nondecreasing, also on the integers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L173-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L173-L179

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

theorem GeneralPieces.Bits.pZ_mono {E E' : ℤ} (h : E ≤ E') : pZ E ≤ pZ E' := by sorry
