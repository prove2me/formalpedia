-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_abs_coef_op_le
-- name    : GeneralPieces.Sizes.abs_coef_op_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:32.612025+00:00
-- url     : https://prove2.me/theorems/5ad3b923-dd00-4c0f-9dff-a091ab4846a5
-- title:
--   Sizes: abs coef op le
-- statement:
--   If all monomials of a have weight at most h, a coefficient of a[r]·t^σ at listed partitions is
--   at most 2^{12h²} times the sum of the absolute values of the coefficients of a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L364-L369
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L364-L369

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

theorem GeneralPieces.Sizes.abs_coef_op_le {h : ℕ} (hh : 1 ≤ h) {a : V} (ha : ∀ m ∈ a.support, Finsupp.weight wgt m ≤ h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h)
    (h2 : wt σ ≤ 4 * h) : |coef σ' (op a r (tpow σ))| ≤ l1 a * 2 ^ (12 * h ^ 2) := by sorry
