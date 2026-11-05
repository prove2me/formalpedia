-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_JpV_mul
-- name    : GeneralPieces.GenF.bra_JpV_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:21.048269+00:00
-- url     : https://prove2.me/theorems/18588875-8344-47bc-9426-e18dc9512043
-- title:
--   Gen F: bra Jp V mul
-- statement:
--   The coefficient of t^σ in J_n^+(v)·f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L302-L305
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L302-L305

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

theorem GeneralPieces.GenF.bra_JpV_mul (σ : Multiset ℕ) (n : ℕ) (f : Tv) :
    bra σ (JpV n * f) = ∑ l ∈ σ.toFinset, ((bet n l : ℚ) • mo 0 ((l : ℤ) - n)) * bra (σ.erase l) f := by sorry
