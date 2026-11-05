-- Prove2me | Theorems.Thm_GeneralPieces_Bits_logb_two_mul_le
-- name    : GeneralPieces.Bits.logb_two_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:51.682099+00:00
-- url     : https://prove2.me/theorems/f1c8c6c3-5f58-4852-9593-22ecaf104001
-- title:
--   Bits: logb two mul le
-- statement:
--   log(2λ) ≤ λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L288-L298
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L288-L298

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

theorem GeneralPieces.Bits.logb_two_mul_le {lam : ℕ} (hl : 1 ≤ lam) : logb 2 (2 * lam) ≤ lam := by sorry
