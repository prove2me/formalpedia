-- Prove2me | Theorems.Thm_Groundwork_Prog_length_he_le
-- name    : Groundwork.Prog.length_he_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:40.649601+00:00
-- url     : https://prove2.me/theorems/6f3af959-d8a7-4425-b1b3-f2a35c3a007f
-- title:
--   Prog: length he le
-- statement:
--   A half-edge read off any word has at most ℓ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Side.lean#L115-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Side.lean#L115-L118

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_CutProg
import Definitions.Def_StepMachines_Math_SideX
import Definitions.Def_StepMachines_Prog_Side
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 rectDig sideChunk sideItem sideCap)

theorem Groundwork.Prog.length_he_le (g ℓ : ℕ) (z : List Bool) (x u : ℕ) : (he g ℓ z x u).length ≤ ℓ := by sorry
