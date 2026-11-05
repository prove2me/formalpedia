-- Prove2me | Theorems.Thm_Groundwork_TM_drp_runs
-- name    : Groundwork.TM.drp_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:02.577346+00:00
-- url     : https://prove2.me/theorems/c882ab1c-f130-4b4f-9e16-676766426fc3
-- title:
--   TM: drp runs
-- statement:
--   `drp i` removes the item x from stack i in |code x| + 1 steps; nothing else changes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L269-L284
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L269-L284

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_TM_Move
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing

theorem Groundwork.TM.drp_runs {i : Stk} (hi : i ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym} (h : S i = code x ++ W) :
    (drp i).Runs none S ((code x).length + 1) (Function.update S i W) := by sorry
