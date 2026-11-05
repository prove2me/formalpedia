-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_abs_entry_le
-- name    : GeneralPieces.Sizes.abs_entry_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:58.66028+00:00
-- url     : https://prove2.me/theorems/93258298-a86f-4e02-b8e3-fef7179b8a84
-- title:
--   Sizes: abs entry le
-- statement:
--   An entry of the table of a monomial with q factors, each t_n with n ≤ h, is at most
--   (32h²·2^{5h})^q in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L159-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L159-L191

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.abs_entry_le {h : ℕ} (hh : 1 ≤ h) (a : List ℕ+) (ha : ∀ n ∈ a, (n : ℕ) ≤ h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (opMon a r (tpow σ))| ≤ (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) ^ a.length := by sorry
