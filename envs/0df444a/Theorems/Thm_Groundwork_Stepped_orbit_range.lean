-- Prove2me | Theorems.Thm_Groundwork_Stepped_orbit_range
-- name    : Groundwork.Stepped.orbit_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:13.457756+00:00
-- url     : https://prove2.me/theorems/ff3f735e-2065-45ac-bc01-184fa26940b4
-- title:
--   Stepped: orbit range
-- statement:
--   The Stepped construction uses the orbit range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L36-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L36-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range
import Definitions.Def_StepMachines_Prog_Range
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Finset
variable {α β γ : Type}

theorem Groundwork.Stepped.orbit_range (N : α → ℕ) (a : α) (k y : ℕ) (h : y + k = N a) :
    Orbit (rangeNext N) (if y < N a then some (a, y) else none) ((List.range' y k).map fun y => (a, y)) := by sorry
