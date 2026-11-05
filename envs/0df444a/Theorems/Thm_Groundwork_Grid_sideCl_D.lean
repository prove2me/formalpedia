-- Prove2me | Theorems.Thm_Groundwork_Grid_sideCl_D
-- name    : Groundwork.Grid.sideCl_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:19.872639+00:00
-- url     : https://prove2.me/theorems/151925e7-8144-4f28-ac7d-5ca6882896f9
-- title:
--   Grid: side Cl D
-- statement:
--   The Grid construction uses the side Cl D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean#L68-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean#L68-L72

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

theorem Groundwork.Grid.sideCl_D (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) :
    (sideCl g tr n R y a b).D = ((vC g n).prod (rectsC g tr n y a b)).D := by sorry
