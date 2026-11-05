-- Prove2me | Theorems.Thm_Groundwork_Stepped_sum_map_range
-- name    : Groundwork.Stepped.sum_map_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:23:16.418196+00:00
-- url     : https://prove2.me/theorems/2875df36-8d4b-40fb-a2cc-e161b33d5cdf
-- title:
--   Stepped: sum map range
-- statement:
--   The Stepped construction uses the sum map range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L44-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L44-L47

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

theorem Groundwork.Stepped.sum_map_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ y ∈ range n, f y := by sorry
