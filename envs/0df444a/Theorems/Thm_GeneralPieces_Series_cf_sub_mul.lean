-- Prove2me | Theorems.Thm_GeneralPieces_Series_cf_sub_mul
-- name    : GeneralPieces.Series.cf_sub_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:40.31341+00:00
-- url     : https://prove2.me/theorems/c6fc6370-b297-4a1f-bf79-100ecdaac90f
-- title:
--   Series: cf sub mul
-- statement:
--   (u − v)·f, coefficient by coefficient.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L189-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L189-L190

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

theorem GeneralPieces.Series.cf_sub_mul (f : S) (x y : ℤ) : cf ((mo 1 0 - mo 0 1) * f) x y = cf f (x - 1) y - cf f x (y - 1) := by sorry
