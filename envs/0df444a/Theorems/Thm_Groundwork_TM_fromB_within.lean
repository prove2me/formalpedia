-- Prove2me | Theorems.Thm_Groundwork_TM_fromB_within
-- name    : Groundwork.TM.fromB_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:52.648028+00:00
-- url     : https://prove2.me/theorems/48e1cef7-74df-4143-8b40-9d46555254f2
-- title:
--   TM: from B within
-- statement:
--   Fetch an item back from stack b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L92-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L92-L96

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

theorem Groundwork.TM.fromB_within : (mv .b .main).Within (st M A (mirror (code x) ++ B) N) ((code x).length + 1)
    (st (code x ++ M) A B N) := by sorry
