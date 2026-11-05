-- Prove2me | Theorems.Thm_GeneralPieces_Series_cf_diag
-- name    : GeneralPieces.Series.cf_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:20.885122+00:00
-- url     : https://prove2.me/theorems/83271ea5-500b-4707-a261-bd62fae12f79
-- title:
--   Series: cf diag
-- statement:
--   The Series construction uses the cf diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L102-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L102-L111

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

theorem GeneralPieces.Series.cf_diag (d : ℤ) (c : ℤ → ℚ) (j₀ x y : ℤ) : cf (diag d c j₀) x y = if j₀ ≤ y ∧ x + y = d then c y else 0 := by sorry
