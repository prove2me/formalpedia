-- Prove2me | Theorems.Thm_GeneralPieces_Series_cf_sub
-- name    : GeneralPieces.Series.cf_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:16:49.608871+00:00
-- url     : https://prove2.me/theorems/3f529c7c-4345-4ff0-82f2-c0baabd3083b
-- title:
--   Series: cf sub
-- statement:
--   The Series construction uses the cf sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L62-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L62-L62

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

theorem GeneralPieces.Series.cf_sub (f g : S) (x y : ℤ) : cf (f - g) x y = cf f x y - cf g x y := by sorry

attribute [defeq] GeneralPieces.Series.cf_sub
