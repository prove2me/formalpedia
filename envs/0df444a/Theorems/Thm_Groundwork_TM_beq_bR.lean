-- Prove2me | Theorems.Thm_Groundwork_TM_beq_bR
-- name    : Groundwork.TM.beq_bR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:21:18.742526+00:00
-- url     : https://prove2.me/theorems/df01a682-d358-4f6a-adcd-efa54b25e005
-- title:
--   TM: beq b R
-- statement:
--   The TM construction uses the beq b R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Tree.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Tree.lean#L31-L31

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

theorem Groundwork.TM.beq_bR (b : Bool) : (Sym.bit b == Sym.R) = false := by sorry
