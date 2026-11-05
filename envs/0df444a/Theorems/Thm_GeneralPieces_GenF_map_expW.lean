-- Prove2me | Theorems.Thm_GeneralPieces_GenF_map_expW
-- name    : GeneralPieces.GenF.map_expW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:20.907922+00:00
-- url     : https://prove2.me/theorems/467b90ca-d40a-4c12-8425-3cffd5f561ab
-- title:
--   Gen F: map exp W
-- statement:
--   A ring homomorphism applied to the coefficients commutes with the exponential.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L151-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L151-L153

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

theorem GeneralPieces.GenF.map_expW {R' : Type} [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (w : MvPowerSeries X R) : map φ (expW w) = expW (map φ w) := by sorry
