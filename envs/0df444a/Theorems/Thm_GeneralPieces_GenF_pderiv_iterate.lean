-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_iterate
-- name    : GeneralPieces.GenF.pderiv_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:10.488287+00:00
-- url     : https://prove2.me/theorems/f53396dd-97b7-4171-bb03-625caf530aed
-- title:
--   Gen F: pderiv iterate
-- statement:
--   ∂/∂x_i 𝒪^{n+1} f = 𝒪^{n+1} ∂f/∂x_i + (n+1)·𝒪ⁿ O_i f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L87-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L87-L95

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

theorem GeneralPieces.GenF.pderiv_iterate {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (n : ℕ) (f : MvPowerSeries X A) :
    pderiv A i ((opX O)^[n + 1] f) = (opX O)^[n + 1] (pderiv A i f) + (n + 1) • (opX O)^[n] (mapE (O i) f) := by sorry
