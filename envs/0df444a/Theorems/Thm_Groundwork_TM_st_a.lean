-- Prove2me | Theorems.Thm_Groundwork_TM_st_a
-- name    : Groundwork.TM.st_a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:25:02.236168+00:00
-- url     : https://prove2.me/theorems/4b176bea-e23c-4547-ae10-d3b01d9143d8
-- title:
--   TM: st a
-- statement:
--   The TM construction uses the st a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean#L39-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean#L39-L39

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

theorem Groundwork.TM.st_a : st M A B N .a = A := by sorry

attribute [defeq] Groundwork.TM.st_a
