-- Prove2me | Theorems.Thm_GeneralPieces_Series_cfP_sumP
-- name    : GeneralPieces.Series.cfP_sumP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:03.152681+00:00
-- url     : https://prove2.me/theorems/f7b22428-d9f6-4d16-812b-4f309e1c3409
-- title:
--   Series: cf P sum P
-- statement:
--   In Σ_{k ≥ 1} c_k·ω₁^{−k−j}·ω₂^{k−n} the coefficient of ω₁^{−k−j}·ω₂^{k−n}, k ≥ 1, is c_k; all
--   other coefficients vanish.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L404-L404
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L404-L404

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

theorem GeneralPieces.Series.cfP_sumP (j n : ℕ) (c : ℤ → ℚ) (x y : ℤ) : cfP (sumP j n c) x y = if 1 ≤ y + n ∧ x + y = -((j : ℤ) + n) then c (y + n) else 0 := by sorry
