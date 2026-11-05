-- Prove2me | Theorems.Thm_Groundwork_Host_pourQ_nil
-- name    : Groundwork.Host.pourQ_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:02.861295+00:00
-- url     : https://prove2.me/theorems/02cbf1cb-7c93-42be-b71e-3429f564044d
-- title:
--   Host: pour Q nil
-- statement:
--   The Host construction uses the pour Q nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L93-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L93-L94

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
variable (W : List Bool) (M A B N : List Sym)

theorem Groundwork.Host.pourQ_nil : TM2.stepAux pourQ none (withIO [] (st M A B N)) = ⟨none, none, withIO [] (st M A B N)⟩ := by sorry
