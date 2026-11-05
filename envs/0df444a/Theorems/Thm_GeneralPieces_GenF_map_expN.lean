-- Prove2me | Theorems.Thm_GeneralPieces_GenF_map_expN
-- name    : GeneralPieces.GenF.map_expN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:26.3697+00:00
-- url     : https://prove2.me/theorems/1af360a2-fa1a-44d5-ab23-e2e1b2c88ced
-- title:
--   Gen F: map exp N
-- statement:
--   A ring homomorphism between rings of power series commutes with the finite sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L144-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L144-L148

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

theorem GeneralPieces.GenF.map_expN {Y R' : Type} [CommRing R'] [Algebra ℚ R'] (Φ : MvPowerSeries X R →+* MvPowerSeries Y R') (N : ℕ) (w : MvPowerSeries X R) :
    Φ (expN N w) = expN N (Φ w) := by sorry
