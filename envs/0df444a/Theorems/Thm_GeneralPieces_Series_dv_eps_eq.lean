-- Prove2me | Theorems.Thm_GeneralPieces_Series_dv_eps_eq
-- name    : GeneralPieces.Series.dv_eps_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:25.625936+00:00
-- url     : https://prove2.me/theorems/0b07b919-07ab-4924-8a3e-54e60f21ae7d
-- title:
--   Series: dv eps eq
-- statement:
--   ∂ε/∂v = Σ_{k ≥ 1} k·u^{−k−1}·v^{k−1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L377-L394
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L377-L394

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

theorem GeneralPieces.Series.dv_eps_eq : dv eps = ser 1 1 fun k => (k : ℚ) := by sorry
