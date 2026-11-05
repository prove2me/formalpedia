-- Prove2me | Theorems.Thm_GeneralPieces_GenF_dsum_Bp
-- name    : GeneralPieces.GenF.dsum_Bp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:12.213195+00:00
-- url     : https://prove2.me/theorems/052d0d71-8fac-4640-8586-9910d52baeff
-- title:
--   Gen F: dsum Bp
-- statement:
--   A⁻ applied to B⁺ is κ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L95-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L95-L114

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

theorem GeneralPieces.GenF.dsum_Bp (rd : Bool) : dsum (DD rd) (Bp rd) = embW (kap rd) := by sorry
