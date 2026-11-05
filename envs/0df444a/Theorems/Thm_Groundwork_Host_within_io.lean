-- Prove2me | Theorems.Thm_Groundwork_Host_within_io
-- name    : Groundwork.Host.within_io
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:47:04.703364+00:00
-- url     : https://prove2.me/theorems/5e093015-d20a-43e9-b2f1-cf8d6f50a051
-- title:
--   Host: within io
-- statement:
--   A fragment over the work stacks keeps its bound in the final machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L50-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L50-L53

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

theorem Groundwork.Host.within_io {P : Fr} {S S' : Stk → List Sym} {t : ℕ} (h : P.Within S t S') (W : List Bool) :
    P.io.Within (withIO W S) t (withIO W S') := by sorry
