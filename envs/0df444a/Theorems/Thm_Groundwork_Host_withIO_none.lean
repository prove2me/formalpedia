-- Prove2me | Theorems.Thm_Groundwork_Host_withIO_none
-- name    : Groundwork.Host.withIO_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:36.462251+00:00
-- url     : https://prove2.me/theorems/c24d34a9-a123-431c-b69d-fadc70360f8b
-- title:
--   Host: with IO none
-- statement:
--   The Host construction uses the with IO none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L55-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L55-L55

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

theorem Groundwork.Host.withIO_none (W : List Bool) (S : Stk → List Sym) : withIO W S none = W := by sorry

attribute [defeq] Groundwork.Host.withIO_none
