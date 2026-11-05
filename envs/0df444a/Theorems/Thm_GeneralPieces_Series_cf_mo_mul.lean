-- Prove2me | Theorems.Thm_GeneralPieces_Series_cf_mo_mul
-- name    : GeneralPieces.Series.cf_mo_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:11.431784+00:00
-- url     : https://prove2.me/theorems/01676bcc-684d-4e5a-a036-b822f6182c13
-- title:
--   Series: cf mo mul
-- statement:
--   Multiplication by a monomial shifts the coefficients.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L81-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L81-L83

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

theorem GeneralPieces.Series.cf_mo_mul (a b : ℤ) (f : S) (x y : ℤ) : cf (mo a b * f) x y = cf f (x - a) (y - b) := by sorry
