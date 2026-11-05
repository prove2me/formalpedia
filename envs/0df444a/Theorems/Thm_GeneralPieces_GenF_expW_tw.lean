-- Prove2me | Theorems.Thm_GeneralPieces_GenF_expW_tw
-- name    : GeneralPieces.GenF.expW_tw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:30.732353+00:00
-- url     : https://prove2.me/theorems/a6e9a36b-aeb9-43ed-a462-795782421743
-- title:
--   Gen F: exp W tw
-- statement:
--   The Gen F construction uses the exp W tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L197-L199
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean#L197-L199

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

theorem GeneralPieces.GenF.expW_tw (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (q : MvPowerSeries X ℚ) : expW (tw wt ε q) = tw wt ε (expW q) := by sorry
