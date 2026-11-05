-- Prove2me | Theorems.Thm_GeneralPieces_GenF_add_pow_div
-- name    : GeneralPieces.GenF.add_pow_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:17.217205+00:00
-- url     : https://prove2.me/theorems/16801648-fa62-42b8-a560-7bd33b879d61
-- title:
--   Gen F: add pow div
-- statement:
--   (a+b)ⁿ/n! = Σ_{i+j=n} (a^i/i!)·(b^j/j!).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L115-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L115-L129

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

theorem GeneralPieces.GenF.add_pow_div (a b : MvPowerSeries X R) (n : ℕ) :
    ((n.factorial : ℚ)⁻¹) • (a + b) ^ n = ∑ p ∈ antidiagonal n, ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • (a ^ p.1 * b ^ p.2) := by sorry
