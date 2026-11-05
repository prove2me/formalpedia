-- Prove2me | Theorems.Thm_Groundwork_Host_build_runs
-- name    : Groundwork.Host.build_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:21.64743+00:00
-- url     : https://prove2.me/theorems/12781da8-6e52-47cd-a9b2-48d47cb6b82f
-- title:
--   Host: build runs
-- statement:
--   The Host construction uses the build runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L122-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L122-L141

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

theorem Groundwork.Host.build_runs (W : List Bool) (B N : List Sym) : ∀ (l suf : List Bool),
    build.Runs none (withIO W (st (wd suf ++ List.replicate l.length .R) (l.map Sym.bit) B N)) (2 * l.length + 1)
      (withIO W (st (wd (l.reverse ++ suf)) [] B N))
  := by sorry
