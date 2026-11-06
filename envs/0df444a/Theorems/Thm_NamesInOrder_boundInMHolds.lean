-- Prove2me | Theorems.Thm_NamesInOrder_boundInMHolds
-- name    : NamesInOrder.boundInMHolds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:42:42.709251+00:00
-- url     : https://prove2.me/theorems/c1bd3056-5562-4cba-9330-5ff4ea054e3c
-- title:
--   Names In Order: bound In MHolds
-- statement:
--   **The first sentence of Theorem A (c)**, at α′ = 1/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Main.lean#L46-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Main.lean#L46-L46

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

theorem NamesInOrder.boundInMHolds : BoundInMHolds := by sorry
