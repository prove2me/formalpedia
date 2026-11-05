-- Prove2me | Theorems.Thm_Groundwork_TM_mv_runs
-- name    : Groundwork.TM.mv_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:15.360186+00:00
-- url     : https://prove2.me/theorems/dab6102a-dab7-43e3-bcc5-af3679586f4a
-- title:
--   TM: mv runs
-- statement:
--   `mv i j` takes the item x off stack i and puts its mirror image on stack j, in |code x| + 1
--   steps; nothing else
--   changes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L237-L250
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L237-L250

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

theorem Groundwork.TM.mv_runs {i j : Stk} (hij : i ≠ j) (hi : i ≠ .cnt) (hj : j ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym}
    (h : S i = code x ++ W) :
    (mv i j).Runs none S ((code x).length + 1) (Function.update (Function.update S i W) j (mirror (code x) ++ S j)) := by sorry
