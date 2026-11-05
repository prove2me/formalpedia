-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_coef_op
-- name    : GeneralPieces.Sizes.coef_op
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:37.665898+00:00
-- url     : https://prove2.me/theorems/ef26bb99-5b6b-4541-b9da-382555c8e329
-- title:
--   Sizes: coef op
-- statement:
--   Each coefficient of a[r]·t^σ is a combination of entries of the tables of the monomials of a,
--   with the coefficients of a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L349-L353
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L349-L353

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.coef_op (a : V) (r : ℤ) (σ' σ : Ptn) :
    coef σ' (op a r (tpow σ)) = ∑ m ∈ a.support, coeff m a * coef σ' (opMon (Finsupp.toMultiset m).toList r (tpow σ)) := by sorry
