-- Prove2me | Theorems.Thm_Groundwork_TM_upd_a
-- name    : Groundwork.TM.upd_a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:26:15.17244+00:00
-- url     : https://prove2.me/theorems/07ae6103-46ed-4c3a-b6da-a1508463d5cc
-- title:
--   TM: upd a
-- statement:
--   The TM construction uses the upd a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean#L44-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean#L44-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Frag
import Definitions.Def_ToTuring_TM_Tree
import Definitions.Def_ToTuring_TM_Stacks
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable (M A B N W : List Sym)

theorem Groundwork.TM.upd_a : Function.update (st M A B N) .a W = st M W B N := by sorry
