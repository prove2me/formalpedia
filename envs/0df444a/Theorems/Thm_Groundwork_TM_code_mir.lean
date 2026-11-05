-- Prove2me | Theorems.Thm_Groundwork_TM_code_mir
-- name    : Groundwork.TM.code_mir
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:16.77509+00:00
-- url     : https://prove2.me/theorems/f5eabc90-66bc-46e3-b59c-41e8de1398da
-- title:
--   TM: code mir
-- statement:
--   The code of the mirrored tree is the mirrored code.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Tree.lean#L64-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Tree.lean#L64-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_ToTuring_TM_Tree
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM

theorem Groundwork.TM.code_mir (x : V) : code x.mir = mirror (code x) := by sorry
