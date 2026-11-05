-- Prove2me | Theorems.Thm_Groundwork_SatNet_mul_size_le
-- name    : Groundwork.SatNet.mul_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:43:43.118253+00:00
-- url     : https://prove2.me/theorems/c20508bd-1a15-450b-9d94-29774827680d
-- title:
--   Sat Net: mul size le
-- statement:
--   With μ = ⌈m/g⌉ clauses a cluster, `g` times the size 2kμ of `sized_net` is at most 2k(m+g).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L498-L501
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L498-L501

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

theorem Groundwork.SatNet.mul_size_le (m g k : ℕ) : g * (2 * k * ((m + g - 1) / g)) ≤ 2 * k * (m + g) := by sorry
