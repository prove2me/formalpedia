-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_expOp
-- name    : GeneralPieces.GenF.pderiv_expOp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:16.85473+00:00
-- url     : https://prove2.me/theorems/0b096147-f67b-414c-8c93-cbb8da1ecd9e
-- title:
--   Gen F: pderiv exp Op
-- statement:
--   ∂/∂x_i (e^𝒪 f) = e^𝒪 (∂f/∂x_i) + e^𝒪 (O_i f), if the O_v commute.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L108-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L108-L112

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

theorem GeneralPieces.GenF.pderiv_expOp {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (f : MvPowerSeries X A) :
    pderiv A i (expOp O f) = expOp O (pderiv A i f) + expOp O (mapE (O i) f) := by sorry
