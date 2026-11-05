-- Prove2me | Theorems.Thm_Groundwork_TM_swapF_within
-- name    : Groundwork.TM.swapF_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:45:42.264559+00:00
-- url     : https://prove2.me/theorems/f6e67a0f-317f-43c7-aa1c-27ae10115dd6
-- title:
--   TM: swap F within
-- statement:
--   The TM construction uses the swap F within property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L109-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L109-L115

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

theorem Groundwork.TM.swapF_within : swapF.Within (st (code x ++ (code y ++ M)) A B N) (2 * ((code x).length + (code y).length) + 4)
    (st (code y ++ (code x ++ M)) A B N) := by sorry
