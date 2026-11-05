-- Prove2me | Theorems.Thm_Groundwork_Grid_ZW_eq_Z
-- name    : Groundwork.Grid.ZW_eq_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:57.947041+00:00
-- url     : https://prove2.me/theorems/870c24bd-b693-4213-a89f-363e074017fb
-- title:
--   Grid: ZW eq Z
-- statement:
--   Z on words is Z with labels in Bits n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L103-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L103-L118

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

theorem Groundwork.Grid.ZW_eq_Z {K : ℕ} (n : ℕ) (Rm : Inst (Fin K) (List Bool)) (d : Bits n) : Inst.ZW n [] Rm = (instW n Rm).Z d := by sorry
