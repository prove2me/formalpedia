-- Prove2me | Theorems.Thm_GeneralPieces_GenF_stTwoOrders
-- name    : GeneralPieces.GenF.stTwoOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:10.779245+00:00
-- url     : https://prove2.me/theorems/fb684cbc-68df-453a-b79b-7623ef778521
-- title:
--   Gen F: st Two Orders
-- statement:
--   The display on the two orders, one half: e^{A⁺}e^{A⁻}·e^{B⁺}e^{B⁻} = e^κ·𝒩, as an equation
--   between the matrix entries. For one value of `rd` this is the equation in 𝓛₊, for the other (A and B
--   exchanged) the one in 𝓛₋.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L148-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L148-L152

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X

theorem GeneralPieces.GenF.stTwoOrders : StTwoOrders := by sorry
