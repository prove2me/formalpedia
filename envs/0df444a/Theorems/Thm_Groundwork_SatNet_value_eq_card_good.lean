-- Prove2me | Theorems.Thm_Groundwork_SatNet_value_eq_card_good
-- name    : Groundwork.SatNet.value_eq_card_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:33.777292+00:00
-- url     : https://prove2.me/theorems/4c9df41d-c110-4450-a1e8-cb9646889eb3
-- title:
--   Sat Net: value eq card good
-- statement:
--   The value counts the states at which all weights and interactions are 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L352-L355
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L352-L355

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
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}

theorem Groundwork.SatNet.value_eq_card_good : (net φ g μ k).value = #{z | Good φ (g := g) (μ := μ) (k := k) z} := by sorry
