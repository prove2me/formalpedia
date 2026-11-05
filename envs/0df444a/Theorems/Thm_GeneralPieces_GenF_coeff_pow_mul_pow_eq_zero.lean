-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_pow_mul_pow_eq_zero
-- name    : GeneralPieces.GenF.coeff_pow_mul_pow_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:10.380776+00:00
-- url     : https://prove2.me/theorems/6bc70be9-ee92-492d-ae1e-b6112ee1811e
-- title:
--   Gen F: coeff pow mul pow eq zero
-- statement:
--   a^i·b^j has no monomials of degree less than i + j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L96-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L96-L105

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

theorem GeneralPieces.GenF.coeff_pow_mul_pow_eq_zero {a b : MvPowerSeries X R} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) {α : X →₀ ℕ} {i j : ℕ}
    (h : α.degree < i + j) : coeff α (a ^ i * b ^ j) = 0 := by sorry
