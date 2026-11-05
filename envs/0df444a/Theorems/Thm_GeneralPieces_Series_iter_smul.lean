-- Prove2me | Theorems.Thm_GeneralPieces_Series_iter_smul
-- name    : GeneralPieces.Series.iter_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:21.616731+00:00
-- url     : https://prove2.me/theorems/a94246b0-cd24-48ca-b5f2-15016da0fa8f
-- title:
--   Series: iter smul
-- statement:
--   The Series construction uses the iter smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L233-L236
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L233-L236

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

theorem GeneralPieces.Series.iter_smul (D : Derivation ℚ A A) (a : ℕ) (r : ℚ) (z : A) : D^[a] (r • z) = r • D^[a] z := by sorry
