-- Prove2me | Theorems.Thm_GeneralPieces_GenF_expD_of_zero
-- name    : GeneralPieces.GenF.expD_of_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:38.709927+00:00
-- url     : https://prove2.me/theorems/5347c45f-ff91-4184-ad3b-5f9e758a449b
-- title:
--   Gen F: exp D of zero
-- statement:
--   e^{Σ x_i D_i} fixes the series on whose coefficients all D_i vanish.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L329-L333
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L329-L333

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

theorem GeneralPieces.GenF.expD_of_zero (D : X → Derivation ℚ A A) {w : MvPowerSeries X A} (h : ∀ i α, D i (coeff α w) = 0) : expD D w = w := by sorry
