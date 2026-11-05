-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_pow_eq_zero
-- name    : GeneralPieces.GenF.coeff_pow_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:17.923551+00:00
-- url     : https://prove2.me/theorems/85eb3fb8-53eb-4b6b-9ecc-10ad06e693d4
-- title:
--   Gen F: coeff pow eq zero
-- statement:
--   wⁿ has no monomials of degree less than n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L71-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L71-L72

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
omit [Algebra ℚ R]

theorem GeneralPieces.GenF.coeff_pow_eq_zero {w : MvPowerSeries X R} (hw : constantCoeff w = 0) {α : X →₀ ℕ} {n : ℕ} (h : α.degree < n) : coeff α (w ^ n) = 0 := by sorry
