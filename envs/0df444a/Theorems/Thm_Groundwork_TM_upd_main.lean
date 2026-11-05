-- Prove2me | Theorems.Thm_Groundwork_TM_upd_main
-- name    : Groundwork.TM.upd_main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:25:25.191573+00:00
-- url     : https://prove2.me/theorems/d5c463f7-9bb4-4822-8737-a31ffc86e6f2
-- title:
--   TM: upd main
-- statement:
--   The TM construction uses the upd main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean#L42-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean#L42-L43

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

theorem Groundwork.TM.upd_main : Function.update (st M A B N) .main W = st W A B N := by sorry
