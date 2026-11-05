-- Prove2me | Theorems.Thm_GeneralPieces_Series_eps_pow_succ
-- name    : GeneralPieces.Series.eps_pow_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:03:25.036546+00:00
-- url     : https://prove2.me/theorems/9f17a962-0977-4781-b3a1-cd16582764f1
-- title:
--   Series: eps pow succ
-- statement:
--   The powers of Σ_{j ≥ 0} u^{−j−1}·v^j: its (N+1)-st power is Σ_{j ≥ 0} C(j+N, N)·u^{−j−N−1}·v^j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L222-L251
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean#L222-L251

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

theorem GeneralPieces.Series.eps_pow_succ (N : ℕ) : eps ^ (N + 1) = diag (-(N : ℤ) - 1) (fun j => ((j.toNat + N).choose N : ℚ)) 0 := by sorry
