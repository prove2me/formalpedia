-- Prove2me | Theorems.Thm_GeneralPieces_Bits_logb_le_of_le_mul_p
-- name    : GeneralPieces.Bits.logb_le_of_le_mul_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:38.736251+00:00
-- url     : https://prove2.me/theorems/933bb81d-7981-471b-ad58-672504e507ba
-- title:
--   Bits: logb le of le mul p
-- statement:
--   By display (46): if 1 ≤ r ≤ k·p(a), then log r ≤ log k + κ√a + C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L208-L216
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L208-L216

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

theorem GeneralPieces.Bits.logb_le_of_le_mul_p (hB : Bounds B C) {r k a : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (h : r ≤ k * p a) :
    logb 2 r ≤ logb 2 k + kappa * √(a : ℝ) + C := by sorry
