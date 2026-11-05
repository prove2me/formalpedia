-- Prove2me | Theorems.Thm_Groundwork_Host_upd_none
-- name    : Groundwork.Host.upd_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:28.159702+00:00
-- url     : https://prove2.me/theorems/5b3cfd7c-b738-4568-9b2f-7ac3d551d56e
-- title:
--   Host: upd none
-- statement:
--   The Host construction uses the upd none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L58-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L58-L59

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

theorem Groundwork.Host.upd_none (W W' : List Bool) (S : Stk → List Sym) : Function.update (withIO W S) none W' = withIO W' S := by sorry
