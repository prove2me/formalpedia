-- Prove2me | Theorems.Thm_GeneralPieces_GenF_borel_step
-- name    : GeneralPieces.GenF.borel_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:27:23.164443+00:00
-- url     : https://prove2.me/theorems/874a27fc-23d1-46f0-8a8f-27121d66aca7
-- title:
--   Gen F: borel step
-- statement:
--   (β + e_i)!·(the coefficient of x^β·x_i in F) = β!·(the coefficient of x^β in ∂F/∂x_i).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L90-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L90-L92

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

theorem GeneralPieces.GenF.borel_step (β : Y →₀ ℕ) (i : Y) (F : MvPowerSeries Y R) :
    fac (β + Finsupp.single i 1) • coeff (β + Finsupp.single i 1) F = fac β • coeff β (pderiv R i F) := by sorry
