-- Prove2me | Theorems.Thm_Groundwork_Host_prologue_within
-- name    : Groundwork.Host.prologue_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:50:48.698165+00:00
-- url     : https://prove2.me/theorems/5f4ee107-9b86-4dd0-b189-3a4f58b60fee
-- title:
--   Host: prologue within
-- statement:
--   The Host construction uses the prologue within property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L146-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L146-L157

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host

theorem Groundwork.Host.prologue_within (x : List Bool) :
    Frag.Within prologue (withIO x (st [] [] [] [])) (4 * x.length + 3) (withIO [] (st (wd x) [] [] [])) := by sorry
