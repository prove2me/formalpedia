-- Prove2me | Theorems.Thm_GeneralPieces_GenF_form_eq_sum
-- name    : GeneralPieces.GenF.form_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:11.538666+00:00
-- url     : https://prove2.me/theorems/f74867f1-2b16-4541-9d98-cf1c9f25e587
-- title:
--   Gen F: form eq sum
-- statement:
--   A linear form on the polynomials in the t_k is determined by its values on the monomials.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/YY.lean#L59-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/YY.lean#L59-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_YY
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset

theorem GeneralPieces.GenF.form_eq_sum (ℓ : Vu →ₗ[Lu] Lu) (p : Vu) : ℓ p = ∑ m ∈ p.support, MvPolynomial.coeff m p * ℓ (MvPolynomial.monomial m 1) := by sorry
