-- Prove2me | Theorems.Thm_GeneralPieces_Bits_exists_kappa_sqrt_le
-- name    : GeneralPieces.Bits.exists_kappa_sqrt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:38.942673+00:00
-- url     : https://prove2.me/theorems/1a7a1c05-cdae-4a3f-8144-e9a44d7e2fbe
-- title:
--   Bits: exists kappa sqrt le
-- statement:
--   And then κ√h ≤ κ√(h−1) + κ ≤ λ + O(log 2λ); on the way, log h = O(log 2λ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L141-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L141-L170

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

theorem GeneralPieces.Bits.exists_kappa_sqrt_le (hB : Bounds B C) : ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ ∀ lam : ℕ, 1 ≤ lam →
    kappa * √(AppHalfPieces.hOf lam : ℝ) ≤ lam + c₁ * logb 2 (2 * lam) ∧ logb 2 (AppHalfPieces.hOf lam) ≤ c₂ * logb 2 (2 * lam) := by sorry
