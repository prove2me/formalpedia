-- Prove2me | Theorems.Thm_Groundwork_TM_st_main
-- name    : Groundwork.TM.st_main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:25:14.674028+00:00
-- url     : https://prove2.me/theorems/d956448b-9a4e-455e-a48d-2a306671f66a
-- title:
--   TM: st main
-- statement:
--   The TM construction uses the st main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean#L38-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean#L38-L38

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

theorem Groundwork.TM.st_main : st M A B N .main = M := by sorry

attribute [defeq] Groundwork.TM.st_main
