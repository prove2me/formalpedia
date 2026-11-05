-- Prove2me | Theorems.Thm_Groundwork_Host_withIO_some
-- name    : Groundwork.Host.withIO_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:36.329981+00:00
-- url     : https://prove2.me/theorems/6976e0c2-3810-4e4a-893d-39a6d8f9ae0f
-- title:
--   Host: with IO some
-- statement:
--   The Host construction uses the with IO some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L56-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L56-L56

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

theorem Groundwork.Host.withIO_some (W : List Bool) (S : Stk → List Sym) (k : Stk) : withIO W S (some k) = S k := by sorry

attribute [defeq] Groundwork.Host.withIO_some
