-- Prove2me | Theorems.Thm_Groundwork_TM_consF_within
-- name    : Groundwork.TM.consF_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:48.459794+00:00
-- url     : https://prove2.me/theorems/11ce67e5-3e82-44de-b858-b9393a8fb399
-- title:
--   TM: cons F within
-- statement:
--   The TM construction uses the cons F within property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L117-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L117-L127

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

theorem Groundwork.TM.consF_within : consF.Within (st (code x ++ (code y ++ M)) A B N) (2 * ((code x).length + (code y).length) + 6)
    (st (code (.cons x y) ++ M) A B N) := by sorry
