-- Prove2me | Theorems.Thm_GeneralPieces_Bits_exists_display_le
-- name    : GeneralPieces.Bits.exists_display_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:03.041449+00:00
-- url     : https://prove2.me/theorems/02cf50cc-e88c-48f5-9af5-c9b8b70c7892
-- title:
--   Bits: exists display le
-- statement:
--   The display, second inequality: 2√2·κ√h + 2·log(2h+1) + 2C + 2 ≤ 2√2·λ + O(log 2λ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L243-L261
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L243-L261

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

theorem GeneralPieces.Bits.exists_display_le (hB : Bounds B C) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam →
    2 * √2 * (kappa * √(AppHalfPieces.hOf lam : ℝ)) + 2 * logb 2 (2 * (AppHalfPieces.hOf lam : ℝ) + 1) + 2 * C + 2 ≤ 2 * √2 * lam + c * logb 2 (2 * lam) := by sorry
