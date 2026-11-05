-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_lin_mul
-- name    : GeneralPieces.GenF.bra_lin_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:48.7725+00:00
-- url     : https://prove2.me/theorems/cba71a0f-502a-48f4-81ab-c56b5d83c384
-- title:
--   Gen F: bra lin mul
-- statement:
--   If every coefficient of g is a linear form in the t_l, the coefficient of t^σ in g·f is the sum
--   over the different parts l of σ of the coefficient of t_l in g times the coefficient of
--   t^{σ − l} in f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L210-L216
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L210-L216

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

theorem GeneralPieces.GenF.bra_lin_mul {g : Tv} (hg : Lin1 g) (σ : Multiset ℕ) (f : Tv) : bra σ (g * f) = ∑ l ∈ σ.toFinset, bra {l} g * bra (σ.erase l) f := by sorry
