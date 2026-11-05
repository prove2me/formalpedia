-- Prove2me | Theorems.Thm_Groundwork_SatNet_mul_add_inj
-- name    : Groundwork.SatNet.mul_add_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:54:50.51723+00:00
-- url     : https://prove2.me/theorems/7427c7c9-4f70-40b5-afdb-55d434cfb587
-- title:
--   Sat Net: mul add inj
-- statement:
--   The Sat Net construction uses the mul add inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L100-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L100-L107

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet
set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}

theorem Groundwork.SatNet.mul_add_inj {k x y j j' : ℕ} (hj : j < k) (hj' : j' < k) (h : x * k + j = y * k + j') :
    x = y ∧ j = j' := by sorry
