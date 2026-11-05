-- Prove2me | Theorems.Thm_GeneralPieces_Series_displayGamma_M
-- name    : GeneralPieces.Series.displayGamma_M
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:03:49.709399+00:00
-- url     : https://prove2.me/theorems/fbcf3616-9fee-4f0f-af7d-83475c07ef9d
-- title:
--   Series: display Gamma M
-- statement:
--   Display (49) for ε₋, with the same number Γ_{j,n}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L296-L298
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L296-L298

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

theorem GeneralPieces.Series.displayGamma_M {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • d1M^[j - 1] (d2M^[n - 1] (epsM ^ 2)) = (ClauseBound.Boson.Gam j n : ℚ) • epsM ^ (j + n) := by sorry
