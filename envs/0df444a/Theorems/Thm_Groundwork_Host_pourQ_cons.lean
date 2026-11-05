-- Prove2me | Theorems.Thm_Groundwork_Host_pourQ_cons
-- name    : Groundwork.Host.pourQ_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:05.557559+00:00
-- url     : https://prove2.me/theorems/e3fd0665-087c-4663-bec9-5c0dd1713dcc
-- title:
--   Host: pour Q cons
-- statement:
--   The Host construction uses the pour Q cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L96-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L96-L98

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

theorem Groundwork.Host.pourQ_cons (b : Bool) : TM2.stepAux pourQ none (withIO (b :: W) (st M A B N)) =
    ⟨some (), none, withIO W (st (.R :: M) (.bit b :: A) B N)⟩ := by sorry
