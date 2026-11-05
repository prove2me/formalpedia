-- Prove2me | Theorems.Thm_Groundwork_TM_Frag_io_runs
-- name    : Groundwork.TM.Frag.io_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:11.600122+00:00
-- url     : https://prove2.me/theorems/fadc1a30-d14b-42de-8074-dc3544955b3e
-- title:
--   Frag: io runs
-- statement:
--   A run of a fragment over the work stacks is a run of the same length of `P.io`, and leaves the
--   bits W as they were.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Lift.lean#L87-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Lift.lean#L87-L89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_Machine_Lift
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing

theorem Groundwork.TM.Frag.io_runs {P : Fr} {v : Option Sym} {S S' : Stk → List Sym} {n : ℕ} (h : P.Runs v S n S') (W : List Bool) :
    P.io.Runs v (withIO W S) n (withIO W S') := by sorry
