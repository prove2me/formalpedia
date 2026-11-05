-- Prove2me | Theorems.Thm_GeneralPieces_Dual_le_of_prod_ne_zero
-- name    : GeneralPieces.Dual.le_of_prod_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:20.10446+00:00
-- url     : https://prove2.me/theorems/3bc0a412-123d-4ad0-967c-7901186bdbe4
-- title:
--   Dual: le of prod ne zero
-- statement:
--   «So a nonzero term has k_i ≥ μ_i for all i».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L251-L265
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L251-L265

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.le_of_prod_ne_zero (μ : List ℕ+) (ks : List ℤ) (hl : ks.length = μ.length) (hpos : ∀ k ∈ ks, 1 ≤ k)
    (h : (List.zipWith theta μ ks).prod ≠ 0) : List.Forall₂ (fun (n : ℕ+) (k : ℤ) => (n : ℤ) ≤ k) μ ks := by sorry
