-- Prove2me | Theorems.Thm_Groundwork_Host_haltList_tmOf
-- name    : Groundwork.Host.haltList_tmOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:36.817138+00:00
-- url     : https://prove2.me/theorems/bcb350e2-b060-47b0-b3a2-38435a836802
-- title:
--   Host: halt List tm Of
-- statement:
--   The Host construction uses the halt List tm Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L277-L284
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L277-L284

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

theorem Groundwork.Host.haltList_tmOf (H : FrIO) (x : List Bool) :
    @Eq (TM2.Cfg Γio H.Λ (Option Sym)) (haltList (tmOf H) x) ⟨none, none, withIO x (st [] [] [] [])⟩ := by sorry
