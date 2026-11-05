-- Prove2me | Theorems.Thm_GeneralPieces_Series_dv_mo
-- name    : GeneralPieces.Series.dv_mo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:03:34.111691+00:00
-- url     : https://prove2.me/theorems/c8643b35-b54c-4f96-9a5c-1bd6fb77a370
-- title:
--   Series: dv mo
-- statement:
--   The Series construction uses the dv mo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L170-L177
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L170-L177

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

theorem GeneralPieces.Series.dv_mo (a b : ℤ) : dv (mo a b) = (b : ℚ) • mo a (b - 1) := by sorry
