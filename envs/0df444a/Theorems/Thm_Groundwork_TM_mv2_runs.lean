-- Prove2me | Theorems.Thm_Groundwork_TM_mv2_runs
-- name    : Groundwork.TM.mv2_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:58.105321+00:00
-- url     : https://prove2.me/theorems/e921ec0a-254a-41c4-bbb9-359e7eba1fe3
-- title:
--   TM: mv2 runs
-- statement:
--   `mv2 i j k` takes the item x off stack i and puts its mirror image on both stacks j and k, in |code
--   x| + 1 steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L262-L266
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L262-L266

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

theorem Groundwork.TM.mv2_runs {i j k : Stk} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : i ≠ .cnt) (hj : j ≠ .cnt) (hk : k ≠ .cnt)
    (x : V) {S : Stk → List Sym} {W : List Sym} (h : S i = code x ++ W) :
    (mv2 i j k).Runs none S ((code x).length + 1)
      (Function.update (Function.update (Function.update S i W) j (mirror (code x) ++ S j)) k (mirror (code x) ++ S k)) := by sorry
