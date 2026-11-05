-- Prove2me | Theorems.Thm_GeneralPieces_Series_dv_sub
-- name    : GeneralPieces.Series.dv_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:03:45.104596+00:00
-- url     : https://prove2.me/theorems/0f0c579a-a3fb-4c4b-a6f7-82ddb8815004
-- title:
--   Series: dv sub
-- statement:
--   The Series construction uses the dv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L183-L185
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L183-L185

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

theorem GeneralPieces.Series.dv_sub : dv (mo 1 0 - mo 0 1) = -1 := by sorry
