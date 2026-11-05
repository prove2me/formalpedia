-- Prove2me | Theorems.Thm_Groundwork_Grid_nodeC_full
-- name    : Groundwork.Grid.nodeC_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:58.288404+00:00
-- url     : https://prove2.me/theorems/ecff190c-4fc0-4835-9ebd-c03d783d1c70
-- title:
--   Grid: node C full
-- statement:
--   The Grid construction uses the node C full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L77-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L77-L78

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

theorem Groundwork.Grid.nodeC_full (g : ℕ) (tr : Bool) (n : ℕ) : (nodeC g tr n).Full := by sorry
