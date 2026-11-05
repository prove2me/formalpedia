-- Prove2me | Theorems.Thm_GeneralPieces_Series_toP_single
-- name    : GeneralPieces.Series.toP_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:35.424356+00:00
-- url     : https://prove2.me/theorems/c4fcd11c-c1f4-4eb9-94fa-e8b5076fb080
-- title:
--   Series: to P single
-- statement:
--   The Series construction uses the to P single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L142-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L142-L142

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

theorem GeneralPieces.Series.toP_single (x y : ℤ) (r : ℚ) : toP (AddMonoidAlgebra.single (x, y) r) = r • mo x y := by sorry
