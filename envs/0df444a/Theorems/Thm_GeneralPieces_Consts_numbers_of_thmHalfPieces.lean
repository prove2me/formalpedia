-- Prove2me | Theorems.Thm_GeneralPieces_Consts_numbers_of_thmHalfPieces
-- name    : GeneralPieces.Consts.numbers_of_thmHalfPieces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:12.234538+00:00
-- url     : https://prove2.me/theorems/91edf483-e5f7-45af-8bba-b792d9d3d2c1
-- title:
--   Consts: numbers of thm Half Pieces
-- statement:
--   What the theorem on the pieces with ρ = 1/√2 says about numbers only: |𝓘| = 4h + 1 ≤ (2λ)^c, d =
--   h! < 2^{(2λ)^c}, and c^row_s + c^col_s ≤ 4ρλ + c·log 2λ for |s| ≤ 2h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Consts.lean#L43-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Consts.lean#L43-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_GeneralPieces_Half_Consts
set_option autoImplicit false
section
section
open GeneralPieces
open Finset Real ClauseBound.Inst.Half
open GeneralPieces.Consts

theorem GeneralPieces.Consts.numbers_of_thmHalfPieces (hT : AppHalfPieces.ThmHalfPiecesPure) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam →
    4 * AppHalfPieces.hOf lam + 1 ≤ (2 * lam) ^ c ∧ (AppHalfPieces.hOf lam).factorial < 2 ^ (2 * lam) ^ c ∧
    ∀ s : ℤ, |s| ≤ 2 * (AppHalfPieces.hOf lam : ℤ) →
      ((Nat.clog 2 (AppHalfPieces.Rrow (AppHalfPieces.hOf lam) s) + Nat.clog 2 (AppHalfPieces.Rcol (AppHalfPieces.hOf lam) s) : ℕ) : ℝ) ≤ 4 * (1 / √2) * lam + c * logb 2 (2 * lam) := by sorry
