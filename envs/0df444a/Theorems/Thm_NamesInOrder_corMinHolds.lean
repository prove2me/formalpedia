-- Prove2me | Theorems.Thm_NamesInOrder_corMinHolds
-- name    : NamesInOrder.corMinHolds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:44:37.799717+00:00
-- url     : https://prove2.me/theorems/f7776d70-7155-449a-bbef-5305379f7994
-- title:
--   Names In Order: cor Min Holds
-- statement:
--   **Corollary 11**.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Main.lean#L43-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Main.lean#L43-L43

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

theorem NamesInOrder.corMinHolds : CorMinHolds := by sorry
