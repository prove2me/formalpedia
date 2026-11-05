-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_coeff_angle
-- name    : GeneralPieces.Sizes.coeff_angle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:30.293824+00:00
-- url     : https://prove2.me/theorems/21eea668-7dea-4029-8535-ba166e66c54d
-- title:
--   Sizes: coeff angle
-- statement:
--   The coefficients of a^⟨i⟩: C(h'+h, i) times those of a at the monomials of weight h' ≤ h, and 0
--   at the others.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L295-L302
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L295-L302

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.coeff_angle (h i : ℕ) (a : V) (m : ℕ+ →₀ ℕ) :
    coeff m (angle h i a) = if Finsupp.weight wgt m ≤ h then ((Finsupp.weight wgt m + h).choose i : ℚ) * coeff m a else 0 := by sorry
