-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_opX
-- name    : GeneralPieces.GenF.pderiv_opX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:04.074858+00:00
-- url     : https://prove2.me/theorems/d98a019b-23a6-4e00-b93f-a5f780e18b1f
-- title:
--   Gen F: pderiv op X
-- statement:
--   ∂/∂x_i ∘ 𝒪 = 𝒪 ∘ ∂/∂x_i + O_i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L59-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L59-L72

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

theorem GeneralPieces.GenF.pderiv_opX (O : X → A →ₗ[ℚ] A) (i : X) (f : MvPowerSeries X A) : pderiv A i (opX O f) = opX O (pderiv A i f) + mapE (O i) f := by sorry
