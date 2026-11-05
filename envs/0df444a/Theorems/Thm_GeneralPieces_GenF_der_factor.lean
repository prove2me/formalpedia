-- Prove2me | Theorems.Thm_GeneralPieces_GenF_der_factor
-- name    : GeneralPieces.GenF.der_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:55.96464+00:00
-- url     : https://prove2.me/theorems/9c541e74-6d0d-4a47-a655-d8d20afce3ae
-- title:
--   Gen F: der factor
-- statement:
--   ∂/∂x_i + (the operator beside x_i in A⁻), on a factor t_k + k·(the coefficient of ∇_k in B⁻) of
--   e^{B⁻}·t^σ'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L159-L169
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L159-L169

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.der_factor (rd : Bool) (i : X) (k : ℕ) :
    MvPowerSeries.pderiv Tv i (MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)) + mapD (DD rd i) (MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)) =
      embW (MvPowerSeries.C ((k : ℚ) • cS rd i (-(k : ℤ)))) := by sorry
