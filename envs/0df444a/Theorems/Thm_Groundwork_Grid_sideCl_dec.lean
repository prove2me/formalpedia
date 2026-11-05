-- Prove2me | Theorems.Thm_Groundwork_Grid_sideCl_dec
-- name    : Groundwork.Grid.sideCl_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:21.10539+00:00
-- url     : https://prove2.me/theorems/e77479a4-1634-4afc-b1af-a4b097d289d5
-- title:
--   Grid: side Cl dec
-- statement:
--   The Grid construction uses the side Cl dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean#L74-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean#L74-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Math_SideX
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {g n : ℕ}

theorem Groundwork.Grid.sideCl_dec (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) :
    (sideCl g tr n R y a b).dec = ((vC g n).prod (rectsC g tr n y a b)).dec := by sorry
