-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_mul_congr
-- name    : GeneralPieces.GenF.coeff_mul_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:19.631996+00:00
-- url     : https://prove2.me/theorems/cc236ea9-3848-42a8-8341-920d9062282a
-- title:
--   Gen F: coeff mul congr
-- statement:
--   The coefficient of α in a product depends only on the coefficients of the monomials of degree at
--   most that of α.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L85-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L85-L92

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

theorem GeneralPieces.GenF.coeff_mul_congr {f f' g g' : MvPowerSeries X R} {α : X →₀ ℕ} (hf : ∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β f = coeff β f')
    (hg : ∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β g = coeff β g') : coeff α (f * g) = coeff α (f' * g') := by sorry
