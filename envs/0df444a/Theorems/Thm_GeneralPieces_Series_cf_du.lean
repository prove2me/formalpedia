-- Prove2me | Theorems.Thm_GeneralPieces_Series_cf_du
-- name    : GeneralPieces.Series.cf_du
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:59.202963+00:00
-- url     : https://prove2.me/theorems/895ece06-17f4-4273-be7e-c63ea1baa396
-- title:
--   Series: cf du
-- statement:
--   ∂/∂u is termwise: the term c·u^{x+1}·v^y becomes (x+1)·c·u^x·v^y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L148-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L148-L152

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial

theorem GeneralPieces.Series.cf_du (f : S) (x y : ℤ) : cf (du f) x y = ((x : ℚ) + 1) * cf f (x + 1) y := by sorry
