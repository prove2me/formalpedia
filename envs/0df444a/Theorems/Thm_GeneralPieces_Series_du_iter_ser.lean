-- Prove2me | Theorems.Thm_GeneralPieces_Series_du_iter_ser
-- name    : GeneralPieces.Series.du_iter_ser
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:10.634624+00:00
-- url     : https://prove2.me/theorems/9e2f1936-f019-447f-9d24-61e3abc645ed
-- title:
--   Series: du iter ser
-- statement:
--   ∂^a/∂u^a of the term u^{−k−p}·v^{k−q} is a!·C(−k−p, a)·u^{−k−p−a}·v^{k−q}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L349-L360
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L349-L360

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

theorem GeneralPieces.Series.du_iter_ser (a p q : ℕ) (c : ℤ → ℚ) :
    du^[a] (ser p q c) = ser (p + a) q fun k => (a.factorial : ℚ) * (Ring.choose (-k - (p : ℤ)) a : ℤ) * c k := by sorry
