-- Prove2me | Theorems.Thm_Groundwork_TM_pop1_within
-- name    : Groundwork.TM.pop1_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:45:38.770532+00:00
-- url     : https://prove2.me/theorems/11196fd0-e6cf-4ca1-bcb8-e47be08e68ce
-- title:
--   TM: pop1 within
-- statement:
--   The TM construction uses the pop1 within property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L64-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L64-L66

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

theorem Groundwork.TM.pop1_within (s : Sym) : pop1.Within (st (s :: M) A B N) 1 (st M A B N) := by sorry
