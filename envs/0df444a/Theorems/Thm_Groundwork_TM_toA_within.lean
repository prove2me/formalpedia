-- Prove2me | Theorems.Thm_Groundwork_TM_toA_within
-- name    : Groundwork.TM.toA_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:52.228448+00:00
-- url     : https://prove2.me/theorems/df6c774d-8310-4231-a1c8-476c4f532618
-- title:
--   TM: to A within
-- statement:
--   Park the item on top of main on stack a (mirrored).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L73-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L73-L76

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

theorem Groundwork.TM.toA_within : (mv .main .a).Within (st (code x ++ M) A B N) ((code x).length + 1)
    (st M (mirror (code x) ++ A) B N) := by sorry
