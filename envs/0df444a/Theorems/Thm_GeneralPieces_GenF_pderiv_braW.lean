-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_braW
-- name    : GeneralPieces.GenF.pderiv_braW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:55.606209+00:00
-- url     : https://prove2.me/theorems/a51b86a3-9fb6-44ec-9a0d-53fddc2424b3
-- title:
--   Gen F: pderiv bra W
-- statement:
--   Taking the coefficient of t^σ commutes with ∂/∂x_i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L381-L385
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L381-L385

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.pderiv_braW (σ : Multiset ℕ) (i : X) (w : W) : MvPowerSeries.pderiv S i (braW σ w) = braW σ (MvPowerSeries.pderiv Tv i w) := by sorry
