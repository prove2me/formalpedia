-- Prove2me | Theorems.Thm_Groundwork_Grid_node_lt
-- name    : Groundwork.Grid.node_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:53.649224+00:00
-- url     : https://prove2.me/theorems/611ff7ad-4c65-41a8-875b-092311b12bba
-- title:
--   Grid: node lt
-- statement:
--   Positions are below g².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L41-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L41-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset

theorem Groundwork.Grid.node_lt {g : ℕ} (tr : Bool) {a i : ℕ} (ha : a < g) (hi : i < g) : node g tr a i < g * g := by sorry
