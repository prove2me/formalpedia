-- Prove2me | Theorems.Thm_Groundwork_TM_mvB_runs
-- name    : Groundwork.TM.mvB_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:48.43921+00:00
-- url     : https://prove2.me/theorems/57fbd0ac-edd8-49ee-9944-27d334b042c9
-- title:
--   TM: mv B runs
-- statement:
--   The loop on its four stacks: one item leaves the source and its mirror image arrives on the
--   chosen targets, in
--   |code| + 1 steps; what lies beneath is not touched.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L175-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L175-L198

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

theorem Groundwork.TM.mvB_runs (p₁ p₂ : Bool) (x : V) (A B₁ B₂ C : List Sym) :
    (mvB p₁ p₂).Runs none (st4 (code x ++ A) B₁ B₂ C) ((code x).length + 1)
      (st4 A (putIf p₁ (mirror (code x)) B₁) (putIf p₂ (mirror (code x)) B₂) C) := by sorry
