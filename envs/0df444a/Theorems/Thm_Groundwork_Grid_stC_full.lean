-- Prove2me | Theorems.Thm_Groundwork_Grid_stC_full
-- name    : Groundwork.Grid.stC_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:09.155991+00:00
-- url     : https://prove2.me/theorems/9dd57cfe-b36d-4020-9378-5f561b73d847
-- title:
--   Grid: st C full
-- statement:
--   The Grid construction uses the st C full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L80-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L80-L81

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

theorem Groundwork.Grid.stC_full (g : ℕ) (tr : Bool) (n : ℕ) : (stC g tr n).Full := by sorry
