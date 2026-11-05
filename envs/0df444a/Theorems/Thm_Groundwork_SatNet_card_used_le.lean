-- Prove2me | Theorems.Thm_Groundwork_SatNet_card_used_le
-- name    : Groundwork.SatNet.card_used_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:38.044425+00:00
-- url     : https://prove2.me/theorems/dde28c9d-d999-4c7b-bdb7-6e7a0402fd7c
-- title:
--   Sat Net: card used le
-- statement:
--   At most `k` slots per clause are used.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L369-L383
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L369-L383

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
omit [DecidableEq V]

theorem Groundwork.SatNet.card_used_le : #{p : Slot g μ k | lit φ p ≠ none} ≤ φ.length * k := by sorry
