-- Prove2me | Theorems.Thm_Groundwork_SatNet_U_net_le
-- name    : Groundwork.SatNet.U_net_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:48.70614+00:00
-- url     : https://prove2.me/theorems/3be273c0-8406-481c-951f-3b5dbc4adfb5
-- title:
--   Sat Net: U net le
-- statement:
--   The label bits `c a b`, summed over all ordered pairs of clusters (`U`), are at most 2k times
--   the number of clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L435-L444
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L435-L444

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

theorem Groundwork.SatNet.U_net_le : (net φ g μ k).U ≤ 2 * k * φ.length := by sorry
