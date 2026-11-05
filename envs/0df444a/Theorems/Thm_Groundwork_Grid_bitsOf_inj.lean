-- Prove2me | Theorems.Thm_Groundwork_Grid_bitsOf_inj
-- name    : Groundwork.Grid.bitsOf_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:08.070514+00:00
-- url     : https://prove2.me/theorems/779c5a3e-e718-4798-83de-e64f4104cb10
-- title:
--   Grid: bits Of inj
-- statement:
--   Two indices are equal iff their words are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L51-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L51-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)

theorem Groundwork.Grid.bitsOf_inj {n : ℕ} {w w' : List Bool} (h : w.length = n) (h' : w'.length = n) :
    bitsOf n w = bitsOf n w' ↔ w = w' := by sorry
