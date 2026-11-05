-- Prove2me | Theorems.Thm_GeneralPieces_GenF_degree_of_coeff_C_mul_X
-- name    : GeneralPieces.GenF.degree_of_coeff_C_mul_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:46.363655+00:00
-- url     : https://prove2.me/theorems/c2200593-0915-4622-ad9b-a56ebcd4df4d
-- title:
--   Gen F: degree of coeff C mul X
-- statement:
--   c·t_k is a linear form.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L228-L234
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L228-L234

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

theorem GeneralPieces.GenF.degree_of_coeff_C_mul_X {c : Lu} {k : ℕ} {m : ℕ →₀ ℕ} (h : MvPolynomial.coeff m (MvPolynomial.C c * MvPolynomial.X k : Vu) ≠ 0) : m.degree = 1 := by sorry
