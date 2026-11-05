-- Prove2me | Theorems.Thm_Groundwork_TM_upd4_src
-- name    : Groundwork.TM.upd4_src
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:01.941403+00:00
-- url     : https://prove2.me/theorems/53c1b37a-afaf-48cf-91e2-3a515dbfb6ce
-- title:
--   TM: upd4 src
-- statement:
--   The TM construction uses the upd4 src property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L99-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L99-L100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_TM_Move
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable (A B₁ B₂ C W : List Sym)

theorem Groundwork.TM.upd4_src : Function.update (st4 A B₁ B₂ C) .src W = st4 W B₁ B₂ C := by sorry
