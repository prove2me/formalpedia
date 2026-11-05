-- Prove2me | Theorems.Thm_NamesInOrder_generalFormFollows
-- name    : NamesInOrder.generalFormFollows
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:14:23.974392+00:00
-- url     : https://prove2.me/theorems/e37a25ff-8dfa-479b-862d-4ffbac367ffc
-- title:
--   Names In Order: general Form Follows
-- statement:
--   The general case, first half, for every machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/General.lean#L40-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/General.lean#L40-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Main
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_Wrap_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_NamesInOrder_General
set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork Wrap TwoMachines MainTheoremForms MinOfBounds
open Sat3 (CNF)

theorem NamesInOrder.generalFormFollows : GeneralFormFollows := by sorry
