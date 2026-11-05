-- Prove2me | Theorems.Thm_GeneralPieces_GenF_mapE_opX
-- name    : GeneralPieces.GenF.mapE_opX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:10.066845+00:00
-- url     : https://prove2.me/theorems/d3ab250e-c418-4bc1-a1df-3dee022a6dca
-- title:
--   Gen F: map E op X
-- statement:
--   O_i, applied to every coefficient, commutes with 𝒪 if the O_v commute.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L75-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L75-L78

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

theorem GeneralPieces.GenF.mapE_opX {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (f : MvPowerSeries X A) : mapE (O i) (opX O f) = opX O (mapE (O i) f) := by sorry
