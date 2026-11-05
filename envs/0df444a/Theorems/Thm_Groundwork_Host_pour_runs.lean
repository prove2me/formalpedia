-- Prove2me | Theorems.Thm_Groundwork_Host_pour_runs
-- name    : Groundwork.Host.pour_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:18.786724+00:00
-- url     : https://prove2.me/theorems/083635d2-1d35-43b6-b6ba-b1c6dd79365c
-- title:
--   Host: pour runs
-- statement:
--   The Host construction uses the pour runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L109-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L109-L120

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

theorem Groundwork.Host.pour_runs (B N : List Sym) : ∀ (x : List Bool) (M A : List Sym),
    pour.Runs none (withIO x (st M A B N)) (2 * x.length + 1)
      (withIO [] (st (List.replicate x.length .R ++ M) ((x.map Sym.bit).reverse ++ A) B N))
  := by sorry
