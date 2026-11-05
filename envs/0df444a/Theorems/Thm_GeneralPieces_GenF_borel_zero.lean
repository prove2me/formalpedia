-- Prove2me | Theorems.Thm_GeneralPieces_GenF_borel_zero
-- name    : GeneralPieces.GenF.borel_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:09:14.358198+00:00
-- url     : https://prove2.me/theorems/2654f8ef-9260-4337-8702-4a4a42c306cc
-- title:
--   Gen F: borel zero
-- statement:
--   α! times the coefficient of x^α = ∏_{i ∈ L} x_i in F is the constant term of the derivative of F
--   with respect to the variables of L.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L103-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L103-L105

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
variable [Algebra ℚ R]

theorem GeneralPieces.GenF.borel_zero (L : List Y) (F : MvPowerSeries Y R) : fac (expo L) • coeff (expo L) F = constantCoeff (pdL L F) := by sorry
