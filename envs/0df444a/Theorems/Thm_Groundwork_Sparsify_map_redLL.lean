-- Prove2me | Theorems.Thm_Groundwork_Sparsify_map_redLL
-- name    : Groundwork.Sparsify.map_redLL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:20.514737+00:00
-- url     : https://prove2.me/theorems/1093b5c7-cdc0-411f-b36b-c0877ef7f89a
-- title:
--   Sparsify: map red LL
-- statement:
--   The Sparsify construction uses the map red LL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyList.lean#L64-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyList.lean#L64-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyStep
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_ThreeSatStatement
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_StepMachines_Math_SparsifyList
set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]

theorem Groundwork.Sparsify.map_redLL (s : List (List α)) : (redLL s).map List.toFinset = redL (s.map List.toFinset) := by sorry
