-- Prove2me | Theorems.Thm_Groundwork_SatNet_good_toState
-- name    : Groundwork.SatNet.good_toState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:35.593507+00:00
-- url     : https://prove2.me/theorems/e00199ef-a7b2-4daf-ad28-e2d8b85bf446
-- title:
--   Sat Net: good to State
-- statement:
--   The Sat Net construction uses the good to State property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L186-L195
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L186-L195

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

theorem Groundwork.SatNet.good_toState (hk : ∀ C ∈ φ, C.length ≤ k) {a : V → Bool} (ha : IsModel φ a) :
    Good φ (toState φ (g := g) (μ := μ) (k := k) a) := by sorry
