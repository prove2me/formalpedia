-- Prove2me | Theorems.Thm_GeneralPieces_GenF_sum_triangle
-- name    : GeneralPieces.GenF.sum_triangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:18.122669+00:00
-- url     : https://prove2.me/theorems/0f049efc-8c12-4a01-be34-133dbbd957a7
-- title:
--   Gen F: sum triangle
-- statement:
--   If F i j = 0 for i + j ≥ N, the sum of F over i + j < N is the sum over i, j < N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L40-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L40-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralPieces_GenF_Exp
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]

theorem GeneralPieces.GenF.sum_triangle {M : Type} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) (h : ∀ i j, N ≤ i + j → F i j = 0) :
    ∑ n ∈ range N, ∑ p ∈ antidiagonal n, F p.1 p.2 = ∑ i ∈ range N, ∑ j ∈ range N, F i j := by sorry
