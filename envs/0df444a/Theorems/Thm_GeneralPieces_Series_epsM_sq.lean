-- Prove2me | Theorems.Thm_GeneralPieces_Series_epsM_sq
-- name    : GeneralPieces.Series.epsM_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:01.458317+00:00
-- url     : https://prove2.me/theorems/f3b99912-5c6c-4f90-91e5-b4c289b1300f
-- title:
--   Series: eps M sq
-- statement:
--   "ε₋² = −∂_{ω₁}ε₋ = Σ_k k·ω₂^{−k−1}·ω₁^{k−1}".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L410-L411
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L410-L411

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

theorem GeneralPieces.Series.epsM_sq : epsM ^ 2 = -d1M epsM ∧ -d1M epsM = sumM 1 1 fun k => (k : ℚ) := by sorry
