-- Prove2me | Theorems.Thm_GeneralPieces_Series_cf_dv
-- name    : GeneralPieces.Series.cf_dv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:30.631356+00:00
-- url     : https://prove2.me/theorems/09bcc248-fa27-452b-8226-477a7488383b
-- title:
--   Series: cf dv
-- statement:
--   ∂/∂v is termwise: the term c·u^x·v^{y+1} becomes (y+1)·c·u^x·v^y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L155-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L155-L159

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

theorem GeneralPieces.Series.cf_dv (f : S) (x y : ℤ) : cf (dv f) x y = ((y : ℚ) + 1) * cf f x (y + 1) := by sorry
