-- Prove2me | Theorems.Thm_GeneralPieces_Series_cf_ser
-- name    : GeneralPieces.Series.cf_ser
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:28.123412+00:00
-- url     : https://prove2.me/theorems/224f2a92-4952-449e-91f1-0cc8773c1acb
-- title:
--   Series: cf ser
-- statement:
--   The Series construction uses the cf ser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L305-L307
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L305-L307

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

theorem GeneralPieces.Series.cf_ser (p q : ℕ) (c : ℤ → ℚ) (x y : ℤ) : cf (ser p q c) x y = if 1 ≤ y + q ∧ x + y = -((p : ℤ) + q) then c (y + q) else 0 := by sorry
