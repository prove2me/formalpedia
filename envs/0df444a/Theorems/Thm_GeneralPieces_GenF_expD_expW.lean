-- Prove2me | Theorems.Thm_GeneralPieces_GenF_expD_expW
-- name    : GeneralPieces.GenF.expD_expW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:44.068952+00:00
-- url     : https://prove2.me/theorems/1e8db110-03dd-4cc4-89b6-364f516c2c05
-- title:
--   Gen F: exp D exp W
-- statement:
--   e^{Σ x_i D_i} commutes with the exponential of power series.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L346-L347
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L346-L347

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Exp
import Mathlib.Algebra.MvPolynomial.Derivation
import Definitions.Def_GeneralPieces_GenF_Taylor
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.GenF.expD_expW (D : X → Derivation ℚ A A) {w : MvPowerSeries X A} (hw : constantCoeff w = 0) : expD D (expW w) = expW (expD D w) := by sorry
