-- Prove2me | Theorems.Thm_Groundwork_Host_chkQ_none
-- name    : Groundwork.Host.chkQ_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:25.627008+00:00
-- url     : https://prove2.me/theorems/470c29ad-e43c-4d1f-9ffb-24acd2406071
-- title:
--   Host: chk Q none
-- statement:
--   The Host construction uses the chk Q none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L180-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L180-L182

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

theorem Groundwork.Host.chkQ_none : TM2.stepAux chkQ none (withIO W (st (wd (none : Option Bool) ++ M) A B N)) =
    ⟨some (), none, withIO W (st M A B N)⟩ := by sorry
