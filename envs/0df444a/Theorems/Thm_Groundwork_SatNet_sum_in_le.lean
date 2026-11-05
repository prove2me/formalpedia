-- Prove2me | Theorems.Thm_Groundwork_SatNet_sum_in_le
-- name    : Groundwork.SatNet.sum_in_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:50.285+00:00
-- url     : https://prove2.me/theorems/ff56ef49-59d2-4b05-be43-d2d3bde82c98
-- title:
--   Sat Net: sum in le
-- statement:
--   The equalities that reach cluster `a` from before.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L407-L414
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L407-L414

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

theorem Groundwork.SatNet.sum_in_le (a : Fin g) : ∑ b, #{s : Sl μ k | Out φ b a s} ≤ #{s : Sl μ k | lit φ (a, s) ≠ none} := by sorry
