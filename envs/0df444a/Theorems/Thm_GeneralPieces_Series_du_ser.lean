-- Prove2me | Theorems.Thm_GeneralPieces_Series_du_ser
-- name    : GeneralPieces.Series.du_ser
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:02.107353+00:00
-- url     : https://prove2.me/theorems/52c668ce-7331-4165-8627-be3f06ee81c7
-- title:
--   Series: du ser
-- statement:
--   ∂/∂u of the term u^{−k−p}·v^{k−q} is (−k−p)·u^{−k−p−1}·v^{k−q}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L320-L333
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L320-L333

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

theorem GeneralPieces.Series.du_ser (p q : ℕ) (c : ℤ → ℚ) : du (ser p q c) = ser (p + 1) q fun k => (-(k : ℚ) - p) * c k := by sorry
