-- Prove2me | Theorems.Thm_Groundwork_Grid_gridE_symm_val
-- name    : Groundwork.Grid.gridE_symm_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:06.406457+00:00
-- url     : https://prove2.me/theorems/3730bf56-353d-49c8-b26e-9871f29d886b
-- title:
--   Grid: grid E symm val
-- statement:
--   The position of a node of the grid among the g² nodes of the instance.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L37-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L37-L38

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

theorem Groundwork.Grid.gridE_symm_val (g : ℕ) (tr : Bool) (w : Fin g × Fin g) : ((gridE g tr).symm w : ℕ) = node g tr w.1 w.2 := by sorry
