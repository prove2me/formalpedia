-- Prove2me | Theorems.Thm_GeneralPieces_Series_smul_ser
-- name    : GeneralPieces.Series.smul_ser
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:25.628202+00:00
-- url     : https://prove2.me/theorems/75becfc8-f2cf-4f64-93d4-71c41f7ae9a9
-- title:
--   Series: smul ser
-- statement:
--   The Series construction uses the smul ser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L312-L317
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L312-L317

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

theorem GeneralPieces.Series.smul_ser (r : ℚ) (p q : ℕ) (c : ℤ → ℚ) : r • ser p q c = ser p q fun k => r * c k := by sorry
