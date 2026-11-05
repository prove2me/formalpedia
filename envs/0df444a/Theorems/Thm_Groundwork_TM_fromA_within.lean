-- Prove2me | Theorems.Thm_Groundwork_TM_fromA_within
-- name    : Groundwork.TM.fromA_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:53.513986+00:00
-- url     : https://prove2.me/theorems/198cb4c6-2216-4a3f-b9c6-fb2c52a855eb
-- title:
--   TM: from A within
-- statement:
--   Fetch an item back from stack a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L85-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L85-L89

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

theorem Groundwork.TM.fromA_within : (mv .a .main).Within (st M (mirror (code x) ++ A) B N) ((code x).length + 1)
    (st (code x ++ M) A B N) := by sorry
