-- Prove2me | Theorems.Thm_GeneralPieces_Series_dv_iter_ser
-- name    : GeneralPieces.Series.dv_iter_ser
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:23.781437+00:00
-- url     : https://prove2.me/theorems/07a85773-beb8-4e5f-814c-c7610c9d5f1a
-- title:
--   Series: dv iter ser
-- statement:
--   ∂^b/∂v^b of the term u^{−k−p}·v^{k−q} is b!·C(k−q, b)·u^{−k−p}·v^{k−q−b}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L363-L374
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L363-L374

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

theorem GeneralPieces.Series.dv_iter_ser (b p q : ℕ) (c : ℤ → ℚ) :
    dv^[b] (ser p q c) = ser p (q + b) fun k => (b.factorial : ℚ) * (Ring.choose (k - (q : ℤ)) b : ℤ) * c k := by sorry
