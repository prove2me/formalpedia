-- Prove2me | Theorems.Thm_GeneralPieces_Series_cf_smul
-- name    : GeneralPieces.Series.cf_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:16:48.239031+00:00
-- url     : https://prove2.me/theorems/c1de338a-17d0-45f3-89ff-6889eb90befd
-- title:
--   Series: cf smul
-- statement:
--   The Series construction uses the cf smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L64-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L64-L64

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

theorem GeneralPieces.Series.cf_smul (r : ℚ) (f : S) (x y : ℤ) : cf (r • f) x y = r * cf f x y := by sorry

attribute [defeq] GeneralPieces.Series.cf_smul
