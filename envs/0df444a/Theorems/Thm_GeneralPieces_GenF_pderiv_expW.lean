-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_expW
-- name    : GeneralPieces.GenF.pderiv_expW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:26:25.167575+00:00
-- url     : https://prove2.me/theorems/df36ec5e-76c2-46aa-ad9d-5fcd60ba7b91
-- title:
--   Gen F: pderiv exp W
-- statement:
--   ∂/∂x_i e^w = (∂w/∂x_i)·e^w.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L46-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L46-L49

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

theorem GeneralPieces.GenF.pderiv_expW (i : X) {w : MvPowerSeries X A} (hw : constantCoeff w = 0) : pderiv A i (expW w) = pderiv A i w * expW w := by sorry
