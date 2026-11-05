-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_abs_fa_le
-- name    : GeneralPieces.ThmHalfPieces.abs_fa_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:27:05.001526+00:00
-- url     : https://prove2.me/theorems/27ded958-a2ae-46b9-82cb-4e02fb0bbe6a
-- title:
--   Thm Half Pieces: abs fa le
-- statement:
--   The first factor is small at listed partitions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L75-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L75-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex

theorem GeneralPieces.ThmHalfPieces.abs_fa_le (hP : PieceFacts) {h : ℕ} (hh : 1 ≤ h) (i : ℕ) {ξ : Ptn} (hξ : wt ξ = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |fa h i r ξ σ' σ| ≤ 2 ^ ClauseBound.Boson.Half.eL h := by sorry
