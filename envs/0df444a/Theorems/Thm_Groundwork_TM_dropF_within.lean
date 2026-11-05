-- Prove2me | Theorems.Thm_Groundwork_TM_dropF_within
-- name    : Groundwork.TM.dropF_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:33.768259+00:00
-- url     : https://prove2.me/theorems/00e60f03-574a-4053-b986-ed084698fc32
-- title:
--   TM: drop F within
-- statement:
--   The TM construction uses the drop F within property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L68-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L68-L70

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

theorem Groundwork.TM.dropF_within : dropF.Within (st (code x ++ M) A B N) ((code x).length + 1) (st M A B N) := by sorry
