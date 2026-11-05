-- Prove2me | Theorems.Thm_GeneralPieces_Bits_exists_bits_le
-- name    : GeneralPieces.Bits.exists_bits_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:05.068621+00:00
-- url     : https://prove2.me/theorems/91087ad9-13d2-4af2-9de4-fa00335fe460
-- title:
--   Bits: exists bits le
-- statement:
--   The display as a whole, in the form of the definition of pieces with ρ = 1/√2: c^row_s + c^col_s
--   ≤ 4ρλ + c·log 2λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L270-L273
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L270-L273

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

theorem GeneralPieces.Bits.exists_bits_le (hB : Bounds B C) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → ∀ s : ℤ, |s| ≤ 2 * (AppHalfPieces.hOf lam : ℤ) →
    ((Nat.clog 2 (Rrow (AppHalfPieces.hOf lam) s) + Nat.clog 2 (Rcol (AppHalfPieces.hOf lam) s) : ℕ) : ℝ) ≤ 4 * (1 / √2) * lam + c * logb 2 (2 * lam) := by sorry
