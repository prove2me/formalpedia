-- Prove2me | Theorems.Thm_Groundwork_SatNet_term_eq
-- name    : Groundwork.SatNet.term_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:47.049439+00:00
-- url     : https://prove2.me/theorems/cea82b56-dc3a-4496-8259-c65dc88f7d63
-- title:
--   Sat Net: term eq
-- statement:
--   The Sat Net construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L324-L349
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L324-L349

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

theorem Groundwork.SatNet.term_eq (z : Fin g → Sl μ k → Bool) :
    (∏ a, (net φ g μ k).W a (z a)) * ∏ p ∈ pairs (Fin g), (net φ g μ k).Ψ p.1 p.2 (z p.1) (z p.2) =
      if Good φ z then 1 else 0 := by sorry
