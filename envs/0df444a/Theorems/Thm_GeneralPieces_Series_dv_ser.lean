-- Prove2me | Theorems.Thm_GeneralPieces_Series_dv_ser
-- name    : GeneralPieces.Series.dv_ser
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:03:54.000275+00:00
-- url     : https://prove2.me/theorems/630e6e40-fbcc-440f-a921-e426a7a78e30
-- title:
--   Series: dv ser
-- statement:
--   ∂/∂v of the term u^{−k−p}·v^{k−q} is (k−q)·u^{−k−p}·v^{k−q−1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L336-L346
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L336-L346

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

theorem GeneralPieces.Series.dv_ser (p q : ℕ) (c : ℤ → ℚ) : dv (ser p q c) = ser p (q + 1) fun k => ((k : ℚ) - q) * c k := by sorry
