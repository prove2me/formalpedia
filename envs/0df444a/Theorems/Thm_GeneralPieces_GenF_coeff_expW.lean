-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_expW
-- name    : GeneralPieces.GenF.coeff_expW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:18.576209+00:00
-- url     : https://prove2.me/theorems/73f3c306-0277-4a34-96cf-18571d98fc83
-- title:
--   Gen F: coeff exp W
-- statement:
--   More terms of the sum do not change the coefficient.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L75-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L75-L80

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

theorem GeneralPieces.GenF.coeff_expW {w : MvPowerSeries X R} (hw : constantCoeff w = 0) {α : X →₀ ℕ} {N : ℕ} (h : α.degree < N) : coeff α (expW w) = coeff α (expN N w) := by sorry
