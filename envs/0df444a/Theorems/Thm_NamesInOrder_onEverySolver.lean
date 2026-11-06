-- Prove2me | Theorems.Thm_NamesInOrder_onEverySolver
-- name    : NamesInOrder.onEverySolver
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:44:32.988432+00:00
-- url     : https://prove2.me/theorems/96807494-ccbe-4b0d-97ee-5564fffa7bd5
-- title:
--   Names In Order: on Every Solver
-- statement:
--   The chain for every solver.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Main.lean#L34-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Main.lean#L34-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_NamesInOrder_Arith
import Definitions.Def_NamesInOrder_Chain
import Definitions.Def_NamesInOrder_General
import Definitions.Def_MainRoute_GeneralMain
import Definitions.Def_PairsToBound_Main
import Definitions.Def_NamesInOrder_Main
set_option autoImplicit false
section
section
open NamesInOrder
open MainRoute PairsToBound

theorem NamesInOrder.onEverySolver : OnEverySolver := by sorry
