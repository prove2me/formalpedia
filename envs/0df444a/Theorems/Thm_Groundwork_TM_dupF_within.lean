-- Prove2me | Theorems.Thm_Groundwork_TM_dupF_within
-- name    : Groundwork.TM.dupF_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:59.958578+00:00
-- url     : https://prove2.me/theorems/d7971838-f36c-4c16-a73a-62b14a45cb7a
-- title:
--   TM: dup F within
-- statement:
--   The TM construction uses the dup F within property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L98-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L98-L107

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

theorem Groundwork.TM.dupF_within :
    dupF.Within (st (code x ++ M) A B N) (3 * (code x).length + 3) (st (code x ++ (code x ++ M)) A B N) := by sorry
