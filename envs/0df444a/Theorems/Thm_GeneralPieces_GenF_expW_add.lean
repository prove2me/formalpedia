-- Prove2me | Theorems.Thm_GeneralPieces_GenF_expW_add
-- name    : GeneralPieces.GenF.expW_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:19.702208+00:00
-- url     : https://prove2.me/theorems/d83d0d97-9236-4107-aca8-956498ad88ce
-- title:
--   Gen F: exp W add
-- statement:
--   e^{a+b} = e^a·e^b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L132-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L132-L141

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

theorem GeneralPieces.GenF.expW_add {a b : MvPowerSeries X R} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) : expW (a + b) = expW a * expW b := by sorry
