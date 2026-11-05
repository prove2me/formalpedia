-- Prove2me | Theorems.Thm_Groundwork_TM_st_cnt
-- name    : Groundwork.TM.st_cnt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:25:12.905826+00:00
-- url     : https://prove2.me/theorems/902af126-85cf-473d-84b1-df104f985b9e
-- title:
--   TM: st cnt
-- statement:
--   The TM construction uses the st cnt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean#L41-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean#L41-L41

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

theorem Groundwork.TM.st_cnt : st M A B N .cnt = N := by sorry

attribute [defeq] Groundwork.TM.st_cnt
