-- Prove2me | Theorems.Thm_Groundwork_TM_toB_within
-- name    : Groundwork.TM.toB_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:50.729701+00:00
-- url     : https://prove2.me/theorems/9b921c37-033d-43e9-b14c-8a5f23a14358
-- title:
--   TM: to B within
-- statement:
--   Park the item on top of main on stack b (mirrored).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L79-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L79-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Move
import Definitions.Def_ToTuring_TM_Ops
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable (x y : V) (M A B N : List Sym)

theorem Groundwork.TM.toB_within : (mv .main .b).Within (st (code x ++ M) A B N) ((code x).length + 1)
    (st M A (mirror (code x) ++ B) N) := by sorry
