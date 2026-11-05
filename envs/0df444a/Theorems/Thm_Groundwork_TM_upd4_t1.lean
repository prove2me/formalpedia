-- Prove2me | Theorems.Thm_Groundwork_TM_upd4_t1
-- name    : Groundwork.TM.upd4_t1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:56.477221+00:00
-- url     : https://prove2.me/theorems/82285f29-ed31-4650-80c2-2d1e2e1d07aa
-- title:
--   TM: upd4 t1
-- statement:
--   The TM construction uses the upd4 t1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L101-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L101-L102

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

theorem Groundwork.TM.upd4_t1 : Function.update (st4 A B₁ B₂ C) .t1 W = st4 A W B₂ C := by sorry
