-- Prove2me | Theorems.Thm_Groundwork_TM_update_withIO
-- name    : Groundwork.TM.update_withIO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:26:43.681606+00:00
-- url     : https://prove2.me/theorems/a6562c0b-d693-41ad-9e22-ce25d2620168
-- title:
--   TM: update with IO
-- statement:
--   Overwriting a work stack commutes with adding the stack of bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Lift.lean#L49-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Lift.lean#L49-L56

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

theorem Groundwork.TM.update_withIO (W : List Bool) (S : Stk → List Sym) (k : Stk) (w : List Sym) :
    Function.update (withIO W S) (some k) w = withIO W (Function.update S k w) := by sorry
