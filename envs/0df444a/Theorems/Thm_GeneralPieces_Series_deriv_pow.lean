-- Prove2me | Theorems.Thm_GeneralPieces_Series_deriv_pow
-- name    : GeneralPieces.Series.deriv_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:15.807994+00:00
-- url     : https://prove2.me/theorems/b70ea6ef-8ac0-4105-8468-0776ffa11128
-- title:
--   Series: deriv pow
-- statement:
--   If Dε = s·ε², then D(ε^m) = s·m·ε^{m+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L239-L242
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L239-L242

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

theorem GeneralPieces.Series.deriv_pow (D : Derivation ℚ A A) {ε : A} {s : ℚ} (h : D ε = s • ε ^ 2) (m : ℕ) : D (ε ^ m) = (s * m) • ε ^ (m + 1) := by sorry
