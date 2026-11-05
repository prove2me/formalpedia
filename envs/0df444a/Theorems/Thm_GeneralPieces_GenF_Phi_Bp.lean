-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Phi_Bp
-- name    : GeneralPieces.GenF.Phi_Bp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:06.766569+00:00
-- url     : https://prove2.me/theorems/ef7144cf-4214-491c-abfc-ba2299a343e8
-- title:
--   Gen F: Phi Bp
-- statement:
--   e^{A⁻} maps B⁺ = Σ_k 𝖡_k·t_k to B⁺ + κ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L117-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L117-L129

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

theorem GeneralPieces.GenF.Phi_Bp (rd : Bool) : Phi rd (Bp rd) = Bp rd + embW (kap rd) := by sorry
