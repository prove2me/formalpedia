-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_linear_mul
-- name    : GeneralPieces.GenF.coeff_linear_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:01.010741+00:00
-- url     : https://prove2.me/theorems/490dd970-112c-45d7-ac46-19a584e11202
-- title:
--   Gen F: coeff linear mul
-- statement:
--   The coefficients of p·q for a linear form p in the t_l.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L181-L202
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L181-L202

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.coeff_linear_mul {p : Vu} (hp : ∀ m, MvPolynomial.coeff m p ≠ 0 → m.degree = 1) (q : Vu) (m : ℕ →₀ ℕ) :
    MvPolynomial.coeff m (p * q) = ∑ l ∈ m.support, MvPolynomial.coeff (Finsupp.single l 1) p * MvPolynomial.coeff (m - Finsupp.single l 1) q := by sorry
