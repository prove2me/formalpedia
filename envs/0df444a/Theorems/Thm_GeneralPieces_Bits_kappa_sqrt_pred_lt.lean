-- Prove2me | Theorems.Thm_GeneralPieces_Bits_kappa_sqrt_pred_lt
-- name    : GeneralPieces.Bits.kappa_sqrt_pred_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:41.796227+00:00
-- url     : https://prove2.me/theorems/67d608b2-d9ae-45a1-bfbf-f72812aaef8f
-- title:
--   Bits: kappa sqrt pred lt
-- statement:
--   By display (46), for B ≥ 0: κ√(h−1) < λ + B·log h + C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L50-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L50-L65

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

theorem GeneralPieces.Bits.kappa_sqrt_pred_lt (hB : Bounds B C) (hB0 : 0 ≤ B) {lam : ℕ} (hl : 1 ≤ lam) :
    kappa * √((AppHalfPieces.hOf lam : ℝ) - 1) < lam + B * logb 2 (AppHalfPieces.hOf lam) + C := by sorry
