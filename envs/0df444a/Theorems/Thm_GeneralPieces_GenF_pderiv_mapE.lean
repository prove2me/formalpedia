-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_mapE
-- name    : GeneralPieces.GenF.pderiv_mapE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:26:26.84312+00:00
-- url     : https://prove2.me/theorems/c5b1226e-19e3-4c6c-ae03-0ff9a32d2135
-- title:
--   Gen F: pderiv map E
-- statement:
--   ∂/∂x_i commutes with a linear map that is applied to every coefficient.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L52-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L52-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Definitions.Def_GeneralPieces_GenF_PDeriv
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.GenF.pderiv_mapE (D : A →ₗ[ℚ] A) (i : X) (f : MvPowerSeries X A) : pderiv A i (mapE D f) = mapE D (pderiv A i f) := by sorry
