-- Prove2me | Theorems.Thm_GeneralPieces_Series_displayGamma_P
-- name    : GeneralPieces.Series.displayGamma_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:03:47.386756+00:00
-- url     : https://prove2.me/theorems/0bb1f507-c8c6-48db-b775-ce8f8f986fef
-- title:
--   Series: display Gamma P
-- statement:
--   Display (49) for ε₊: (1/((j−1)!(n−1)!))·∂_{ω₁}^{j−1}∂_{ω₂}^{n−1}ε₊² = Γ_{j,n}·ε₊^{j+n}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L291-L293
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L291-L293

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

theorem GeneralPieces.Series.displayGamma_P {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • d1P^[j - 1] (d2P^[n - 1] (epsP ^ 2)) = (ClauseBound.Boson.Gam j n : ℚ) • epsP ^ (j + n) := by sorry
