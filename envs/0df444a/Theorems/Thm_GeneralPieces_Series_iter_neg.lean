-- Prove2me | Theorems.Thm_GeneralPieces_Series_iter_neg
-- name    : GeneralPieces.Series.iter_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:03:51.399536+00:00
-- url     : https://prove2.me/theorems/ab6f6d1e-d14c-4e27-bb99-fe5ed4a6bb01
-- title:
--   Series: iter neg
-- statement:
--   D₁^a(ε^m) = a!·C(−m, a)·ε^{m+a}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L256-L269
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L256-L269

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
variable {A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.Series.iter_neg (D : Derivation ℚ A A) {ε : A} (h : D ε = -ε ^ 2) (a m : ℕ) :
    D^[a] (ε ^ m) = ((a.factorial : ℚ) * (Ring.choose (-(m : ℤ)) a : ℤ)) • ε ^ (m + a) := by sorry
