-- Prove2me | Theorems.Thm_Groundwork_SatNet_Link_used_left
-- name    : Groundwork.SatNet.Link.used_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:43.394024+00:00
-- url     : https://prove2.me/theorems/cf26ebc5-cc4a-48b6-a333-7d574df51616
-- title:
--   Link: used left
-- statement:
--   The Link construction uses the used left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L360-L361
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L360-L361

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

theorem Groundwork.SatNet.Link.used_left {p q : Slot g μ k} (h : Link φ p q) : lit φ p ≠ none := by sorry
