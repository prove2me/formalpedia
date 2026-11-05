-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_coef_comp_gen
-- name    : GeneralPieces.Pcs.coef_comp_gen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:24:17.931423+00:00
-- url     : https://prove2.me/theorems/400118cd-11af-4f36-a4da-d7b6ffdefca1
-- title:
--   Pcs: coef comp gen
-- statement:
--   "Expanding these polynomials in monomials t^σ": if f ∈ V_E, then b[r']f ∈ V_{E+r'} by (O1), and
--   the coefficient of t^π in a[r]b[r']f is the sum over |σ| = E + r' of the coefficient of t^π in
--   a[r]t^σ times the coefficient of t^σ in b[r']f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L214-L218
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L214-L218

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem GeneralPieces.Pcs.coef_comp_gen (hOp : OpFacts) (h1 : O1) (a b : V) (r r' : ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) (π : Ptn) :
    coef π (op a r (op b r' f)) = ∑ σ ∈ ptnsZ (E + r'), coef π (op a r (tpow σ)) * coef σ (op b r' f) := by sorry
