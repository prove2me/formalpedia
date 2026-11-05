-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_coef_comp
-- name    : GeneralPieces.LemQ.coef_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:20.050065+00:00
-- url     : https://prove2.me/theorems/2014d7bd-4ac6-4c5d-9987-ef5cbb302c8d
-- title:
--   Lem Q: coef comp
-- statement:
--   The coefficients of a[r]b[r']t^σ, for monomials a and b, are the entries of the product of the
--   two matrices: by (O1), b[r']t^σ is a combination of the t^τ with |τ| = |σ| + r'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L298-L307
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L298-L307

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

theorem GeneralPieces.LemQ.coef_comp (hB : StBridge) (hOp : OpFacts) (h1 : O1) (μ ν : Ptn) (r r' : ℤ) (π σ : Ptn) :
    coef π (op (tpow μ) r (op (tpow ν) r' (tpow σ))) = (ClauseBound.Boson.mul2 (lst μ) r (lst ν) r' (toN π) (toN σ) : ℚ) := by sorry
