-- Prove2me | Theorems.Thm_Groundwork_SatNet_toState_inj
-- name    : Groundwork.SatNet.toState_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:28.543132+00:00
-- url     : https://prove2.me/theorems/b2f42824-db4c-4897-8999-65c3237c5675
-- title:
--   Sat Net: to State inj
-- statement:
--   The Sat Net construction uses the to State inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L235-L245
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L235-L245

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

theorem Groundwork.SatNet.toState_inj (hk : ∀ C ∈ φ, C.length ≤ k) (hm : φ.length ≤ g * μ) {a a' : V → Bool}
    (ha : IsModel φ a) (ha' : IsModel φ a')
    (h : toState φ (g := g) (μ := μ) (k := k) a = toState φ a') : a = a' := by sorry
