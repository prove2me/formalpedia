-- Prove2me | Theorems.Thm_GeneralPieces_Series_eps_mul_sub
-- name    : GeneralPieces.Series.eps_mul_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:49.137547+00:00
-- url     : https://prove2.me/theorems/c555fb8e-d80d-41c3-af4c-bbf836ef51f3
-- title:
--   Series: eps mul sub
-- statement:
--   The Series construction uses the eps mul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L187-L187
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L187-L187

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

theorem GeneralPieces.Series.eps_mul_sub : eps * (mo 1 0 - mo 0 1) = 1 := by sorry
