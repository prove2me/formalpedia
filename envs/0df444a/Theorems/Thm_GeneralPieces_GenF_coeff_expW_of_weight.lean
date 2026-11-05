-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_expW_of_weight
-- name    : GeneralPieces.GenF.coeff_expW_of_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:31.937889+00:00
-- url     : https://prove2.me/theorems/6b4fd9e2-bab1-4bb4-b31d-f2e2a551f5e3
-- title:
--   Gen F: coeff exp W of weight
-- statement:
--   If the coefficient of every monomial α in w is q_α·ε^{wt α} with a rational number q_α, then its
--   coefficient in e^w is (the coefficient of α in e^q)·ε^{wt α}: the number is the same for every ε and
--   every R.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L204-L207
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L204-L207

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

theorem GeneralPieces.GenF.coeff_expW_of_weight (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (q : MvPowerSeries X ℚ) {w : MvPowerSeries X R}
    (hw : ∀ α, coeff α w = algebraMap ℚ R (coeff α q) * ε ^ wt α) (α : X →₀ ℕ) : coeff α (expW w) = algebraMap ℚ R (coeff α (expW q)) * ε ^ wt α := by sorry
