-- Prove2me | Theorems.Thm_Groundwork_SatNet_sum_c_le
-- name    : Groundwork.SatNet.sum_c_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:46.127016+00:00
-- url     : https://prove2.me/theorems/d988466f-04d9-4f9a-9954-770fb2ab3837
-- title:
--   Sat Net: sum c le
-- statement:
--   The Sat Net construction uses the sum c le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L423-L431
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L423-L431

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

theorem Groundwork.SatNet.sum_c_le (a : Fin g) :
    ∑ b ∈ univ.erase a, (net φ g μ k).c a b ≤ 2 * #{s : Sl μ k | lit φ (a, s) ≠ none} := by sorry
