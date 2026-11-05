-- Prove2me | Theorems.Thm_GeneralPieces_Series_du_mo
-- name    : GeneralPieces.Series.du_mo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:03:33.623243+00:00
-- url     : https://prove2.me/theorems/2903aafa-150c-4325-8e1f-b59846b4be40
-- title:
--   Series: du mo
-- statement:
--   The Series construction uses the du mo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L161-L168
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L161-L168

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

theorem GeneralPieces.Series.du_mo (a b : ℤ) : du (mo a b) = (a : ℚ) • mo (a - 1) b := by sorry
