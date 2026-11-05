-- Prove2me | Theorems.Thm_GeneralPieces_GenF_expD_of_sq_zero
-- name    : GeneralPieces.GenF.expD_of_sq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:46.296452+00:00
-- url     : https://prove2.me/theorems/49c5eecd-266d-4a31-93ce-3ef52ad53bd6
-- title:
--   Gen F: exp D of sq zero
-- statement:
--   Taylor's formula: e^{Σ x_i D_i} w = w + Σ_i x_i·D_i w, if all D_i D_j vanish on the coefficients
--   of w.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L337-L343
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L337-L343

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

theorem GeneralPieces.GenF.expD_of_sq_zero (D : X → Derivation ℚ A A) {w : MvPowerSeries X A} (h : ∀ i j α, D i (D j (coeff α w)) = 0) : expD D w = w + dsum D w := by sorry
