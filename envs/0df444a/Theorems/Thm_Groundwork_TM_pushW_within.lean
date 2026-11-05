-- Prove2me | Theorems.Thm_Groundwork_TM_pushW_within
-- name    : Groundwork.TM.pushW_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:44.903521+00:00
-- url     : https://prove2.me/theorems/4f39426f-2da1-403a-b423-0e7ab09dcc92
-- title:
--   TM: push W within
-- statement:
--   The TM construction uses the push W within property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L60-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L60-L62

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

theorem Groundwork.TM.pushW_within (w : List Sym) : (pushW w).Within (st M A B N) 1 (st (w ++ M) A B N) := by sorry
