-- Prove2me | Theorems.Thm_GeneralPieces_Series_cf_sum
-- name    : GeneralPieces.Series.cf_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:24.368201+00:00
-- url     : https://prove2.me/theorems/c4d6f900-57f2-4141-a9db-15638b3593eb
-- title:
--   Series: cf sum
-- statement:
--   The coefficients of a finite sum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L86-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L86-L90

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

theorem GeneralPieces.Series.cf_sum {α : Type} (s : Finset α) (g : α → S) (x y : ℤ) : cf (∑ c ∈ s, g c) x y = ∑ c ∈ s, cf (g c) x y := by sorry
