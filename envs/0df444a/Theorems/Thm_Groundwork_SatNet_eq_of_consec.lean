-- Prove2me | Theorems.Thm_Groundwork_SatNet_eq_of_consec
-- name    : Groundwork.SatNet.eq_of_consec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:53.194191+00:00
-- url     : https://prove2.me/theorems/25adae86-0f98-4865-ba39-c7311b051d0d
-- title:
--   Sat Net: eq of consec
-- statement:
--   Equal on consecutive occurrences implies equal on all occurrences of a variable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L66-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L66-L83

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
variable {ι V : Type}
variable {idx : ι → ℕ} {lab : ι → Option V}

theorem Groundwork.SatNet.eq_of_consec (hidx : Function.Injective idx) {z : ι → Bool}
    (hz : ∀ p q, Consec idx lab p q → z p = z q) {p q : ι} (hp : lab p ≠ none) (hpq : lab p = lab q) :
    z p = z q := by sorry
