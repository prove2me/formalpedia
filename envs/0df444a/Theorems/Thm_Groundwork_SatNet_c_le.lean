-- Prove2me | Theorems.Thm_Groundwork_SatNet_c_le
-- name    : Groundwork.SatNet.c_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:49.339479+00:00
-- url     : https://prove2.me/theorems/fa55b343-83a1-4706-aa76-a29bcefbdc92
-- title:
--   Sat Net: c le
-- statement:
--   The Sat Net construction uses the c le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L416-L421
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L416-L421

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

theorem Groundwork.SatNet.c_le (a b : Fin g) :
    (net φ g μ k).c a b ≤ #{s : Sl μ k | Out φ a b s} + #{s : Sl μ k | Out φ b a s} := by sorry
