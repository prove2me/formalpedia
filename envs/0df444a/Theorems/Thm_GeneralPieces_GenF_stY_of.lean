-- Prove2me | Theorems.Thm_GeneralPieces_GenF_stY_of
-- name    : GeneralPieces.GenF.stY_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:31.794204+00:00
-- url     : https://prove2.me/theorems/39a30816-1b84-46a5-b4d5-b741af971784
-- title:
--   Gen F: st Y of
-- statement:
--   μ!·ν! times the coefficient of x^μ·x'^ν in ⟨e^{A⁺}e^{A⁻}·e^{B⁺}e^{B⁻}⟩ is f₊ = ⟨Y(a, u)·Y(b,
--   v)⟩, from the expansions of the two pairs of exponentials.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/YY.lean#L118-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/YY.lean#L118-L127

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_YY
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset

theorem GeneralPieces.GenF.stY_of (h1 : StY1) (h1' : StY1') (h0 : StOp0) (h2 : StY2) (hxo : StXo) : StY := by sorry
