-- Prove2me | Theorems.Thm_GeneralPieces_GenF_hom_expW
-- name    : GeneralPieces.GenF.hom_expW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:19.325003+00:00
-- url     : https://prove2.me/theorems/4b0d72c0-2320-485f-aba2-9444e233637a
-- title:
--   Gen F: hom exp W
-- statement:
--   A ring homomorphism Φ of the ring of power series commutes with the exponential, if the
--   coefficient of α in Φ f depends only on the coefficients of f at the monomials of degree at most
--   that of α.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L158-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L158-L162

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

theorem GeneralPieces.GenF.hom_expW (Φ : MvPowerSeries X R →+* MvPowerSeries X R)
    (hΦ : ∀ (α : X →₀ ℕ) (f g : MvPowerSeries X R), (∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β f = coeff β g) → coeff α (Φ f) = coeff α (Φ g))
    {w : MvPowerSeries X R} (hw : constantCoeff w = 0) : Φ (expW w) = expW (Φ w) := by sorry
