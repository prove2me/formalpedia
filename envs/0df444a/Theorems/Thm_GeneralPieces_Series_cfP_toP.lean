-- Prove2me | Theorems.Thm_GeneralPieces_Series_cfP_toP
-- name    : GeneralPieces.Series.cfP_toP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:11.890196+00:00
-- url     : https://prove2.me/theorems/1bdc67c0-b184-4fac-bd24-fc4fd0da5783
-- title:
--   Series: cf P to P
-- statement:
--   An element of 𝓛 has the same coefficients in 𝓛₊.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L151-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L151-L162

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Definitions.Def_GeneralPieces_Series_Rings
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial

theorem GeneralPieces.Series.cfP_toP (F : L) (x y : ℤ) : cfP (toP F) x y = F.coeff (x, y) := by sorry
