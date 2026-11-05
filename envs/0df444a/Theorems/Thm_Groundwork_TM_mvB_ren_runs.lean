-- Prove2me | Theorems.Thm_Groundwork_TM_mvB_ren_runs
-- name    : Groundwork.TM.mvB_ren_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:07.287284+00:00
-- url     : https://prove2.me/theorems/1ec32829-7b20-4974-964f-397e94b7a59d
-- title:
--   TM: mv B ren runs
-- statement:
--   The loop on the work stacks: source i, targets j and k, all different, and the counter.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L214-L229
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L214-L229

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

theorem Groundwork.TM.mvB_ren_runs (p₁ p₂ : Bool) {i j k : Stk} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : i ≠ .cnt)
    (hj : j ≠ .cnt) (hk : k ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym} (h : S i = code x ++ W) :
    ((mvB p₁ p₂).ren (toStk i j k)).Runs none S ((code x).length + 1)
      (Function.update (Function.update (Function.update S i W) j (putIf p₁ (mirror (code x)) (S j))) k
        (putIf p₂ (mirror (code x)) (S k))) := by sorry
