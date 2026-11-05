-- Prove2me | Theorems.Thm_Groundwork_TM_st4_src
-- name    : Groundwork.TM.st4_src
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:59.014535+00:00
-- url     : https://prove2.me/theorems/f86c1cc0-ef76-4117-956a-f05fe6704bc9
-- title:
--   TM: st4 src
-- statement:
--   The TM construction uses the st4 src property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L95-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L95-L95

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

theorem Groundwork.TM.st4_src : st4 A B₁ B₂ C .src = A := by sorry

attribute [defeq] Groundwork.TM.st4_src
