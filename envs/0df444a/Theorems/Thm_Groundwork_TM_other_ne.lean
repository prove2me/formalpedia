-- Prove2me | Theorems.Thm_Groundwork_TM_other_ne
-- name    : Groundwork.TM.other_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:22.908005+00:00
-- url     : https://prove2.me/theorems/245d71e7-bd0a-4121-955d-5827b198a184
-- title:
--   TM: other ne
-- statement:
--   The TM construction uses the other ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L231-L232
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L231-L232

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

theorem Groundwork.TM.other_ne (i j : Stk) : other i j ≠ i ∧ other i j ≠ j ∧ other i j ≠ .cnt := by sorry
