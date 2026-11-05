-- Prove2me | Theorems.Thm_GeneralPieces_Series_displayGamma
-- name    : GeneralPieces.Series.displayGamma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:11.056518+00:00
-- url     : https://prove2.me/theorems/2dc331b3-f67d-4e10-b2e8-4d9ceaeab76d
-- title:
--   Series: display Gamma
-- statement:
--   Display (49) with Γ_{j,n} = n·C(−n−1, j−1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L272-L286
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L272-L286

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
variable {A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.Series.displayGamma (D₁ D₂ : Derivation ℚ A A) {ε : A} (h₁ : D₁ ε = -ε ^ 2) (h₂ : D₂ ε = ε ^ 2) {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • D₁^[j - 1] (D₂^[n - 1] (ε ^ 2)) = (ClauseBound.Boson.Gam j n : ℚ) • ε ^ (j + n) := by sorry
