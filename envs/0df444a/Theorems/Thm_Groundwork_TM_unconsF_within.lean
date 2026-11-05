-- Prove2me | Theorems.Thm_Groundwork_TM_unconsF_within
-- name    : Groundwork.TM.unconsF_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:50.944935+00:00
-- url     : https://prove2.me/theorems/8b33480d-4a47-474c-964e-a46a45ab4c0c
-- title:
--   TM: uncons F within
-- statement:
--   The TM construction uses the uncons F within property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L129-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean#L129-L139

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

theorem Groundwork.TM.unconsF_within : unconsF.Within (st (code (.cons x y) ++ M) A B N) (2 * ((code x).length + (code y).length) + 6)
    (st (code x ++ (code y ++ M)) A B N) := by sorry
