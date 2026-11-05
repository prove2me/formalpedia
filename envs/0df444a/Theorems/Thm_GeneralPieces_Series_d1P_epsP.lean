-- Prove2me | Theorems.Thm_GeneralPieces_Series_d1P_epsP
-- name    : GeneralPieces.Series.d1P_epsP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:03:45.130475+00:00
-- url     : https://prove2.me/theorems/05bf1776-7b67-45ab-9c1a-b3f7330bc623
-- title:
--   Series: d1 P eps P
-- statement:
--   "Differentiating (ω₁ − ω₂)·ε₊ = 1 gives ∂_{ω₁}ε₊ = −ε₊²".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L213-L213
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L213-L213

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

theorem GeneralPieces.Series.d1P_epsP : d1P epsP = -epsP ^ 2 := by sorry
