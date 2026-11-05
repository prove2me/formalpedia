-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_rat_smul
-- name    : GeneralPieces.GenF.coeff_rat_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:35.080464+00:00
-- url     : https://prove2.me/theorems/2b4a030f-b405-4cd9-894e-f62156c11a19
-- title:
--   Gen F: coeff rat smul
-- statement:
--   The Gen F construction uses the coeff rat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L67-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L67-L67

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

theorem GeneralPieces.GenF.coeff_rat_smul (α : X →₀ ℕ) (q : ℚ) (f : MvPowerSeries X R) : coeff α (q • f) = q • coeff α f := by sorry
