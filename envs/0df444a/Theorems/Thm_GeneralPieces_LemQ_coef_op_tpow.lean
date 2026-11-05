-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_coef_op_tpow
-- name    : GeneralPieces.LemQ.coef_op_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:18.333979+00:00
-- url     : https://prove2.me/theorems/cd4d6915-3237-4e95-ac23-ea869958c493
-- title:
--   Lem Q: coef op tpow
-- statement:
--   The coefficients of a[r]t^σ, for a monomial a, are the entries of the matrix.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L268-L273
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L268-L273

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.LemQ.coef_op_tpow (hB : StBridge) (hOp : OpFacts) (μ : Ptn) (r : ℤ) (π σ : Ptn) :
    coef π (op (tpow μ) r (tpow σ)) = (ClauseBound.Boson.op (lst μ) r (toN π) (toN σ) : ℚ) := by sorry
