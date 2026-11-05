-- Prove2me | Theorems.Thm_Groundwork_Grid_bitsOf_eq_zero
-- name    : Groundwork.Grid.bitsOf_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:02.857102+00:00
-- url     : https://prove2.me/theorems/b7adfb05-1258-4bec-9a95-cf2fd9a5c8d5
-- title:
--   Grid: bits Of eq zero
-- statement:
--   A word names the index 0…0 iff all its bits are false.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L56-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L56-L70

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

theorem Groundwork.Grid.bitsOf_eq_zero {n : ℕ} {w : List Bool} (h : w.length = n) :
    bitsOf n w = (fun _ => false) ↔ w.all (!·) = true := by sorry
