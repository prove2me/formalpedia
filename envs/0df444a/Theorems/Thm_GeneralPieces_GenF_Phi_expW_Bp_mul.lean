-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Phi_expW_Bp_mul
-- name    : GeneralPieces.GenF.Phi_expW_Bp_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:12.09544+00:00
-- url     : https://prove2.me/theorems/879b53cf-dda2-4955-9bf6-e5ea83409209
-- title:
--   Gen F: Phi exp W Bp mul
-- statement:
--   e^{A⁻}·e^{B⁺} = e^κ·e^{B⁺}·e^{A⁻}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L135-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L135-L143

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

theorem GeneralPieces.GenF.Phi_expW_Bp_mul (rd : Bool) (w : W) : Phi rd (expW (Bp rd) * w) = embW (expW (kap rd)) * (expW (Bp rd) * Phi rd w) := by sorry
