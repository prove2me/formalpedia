-- Prove2me | Theorems.Thm_Groundwork_SatNet_sum_card_eq
-- name    : Groundwork.SatNet.sum_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:43:38.115004+00:00
-- url     : https://prove2.me/theorems/e961f314-0e78-4a19-aba0-b51762af37b5
-- title:
--   Sat Net: sum card eq
-- statement:
--   The Sat Net construction uses the sum card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L385-L388
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L385-L388

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

theorem Groundwork.SatNet.sum_card_eq (P : Fin g → Sl μ k → Prop) [∀ b s, Decidable (P b s)] :
    ∑ b, #{s | P b s} = #{q : Slot g μ k | P q.1 q.2} := by sorry
