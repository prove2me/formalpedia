-- Prove2me | Theorems.Thm_GeneralPieces_Bits_kappa_sqrt_le_pred
-- name    : GeneralPieces.Bits.kappa_sqrt_le_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:48.389872+00:00
-- url     : https://prove2.me/theorems/b7d2330f-b009-4ced-b009-05477e5a06d1
-- title:
--   Bits: kappa sqrt le pred
-- statement:
--   κ√h ≤ κ√(h−1) + κ, for h ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L129-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L129-L138

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

theorem GeneralPieces.Bits.kappa_sqrt_le_pred {h : ℕ} (hh : 1 ≤ h) : kappa * √(h : ℝ) ≤ kappa * √((h : ℝ) - 1) + kappa := by sorry
