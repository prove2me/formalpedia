-- Prove2me | Theorems.Thm_GeneralPieces_Series_sub_mul_eps
-- name    : GeneralPieces.Series.sub_mul_eps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:32.091139+00:00
-- url     : https://prove2.me/theorems/47ba0814-bb9a-4fbd-84db-7f7dcd45181e
-- title:
--   Series: sub mul eps
-- statement:
--   (u − v)·Σ_{j ≥ 0} u^{−j−1}·v^j = 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L195-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L195-L198

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

theorem GeneralPieces.Series.sub_mul_eps : (mo 1 0 - mo 0 1) * eps = 1 := by sorry
