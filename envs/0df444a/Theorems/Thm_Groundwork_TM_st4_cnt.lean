-- Prove2me | Theorems.Thm_Groundwork_TM_st4_cnt
-- name    : Groundwork.TM.st4_cnt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:53.062966+00:00
-- url     : https://prove2.me/theorems/36f542e9-1702-4c8d-b4a1-467f0b16005b
-- title:
--   TM: st4 cnt
-- statement:
--   The TM construction uses the st4 cnt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L98-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L98-L98

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

theorem Groundwork.TM.st4_cnt : st4 A B₁ B₂ C .cnt = C := by sorry

attribute [defeq] Groundwork.TM.st4_cnt
