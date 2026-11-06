-- Prove2me | Theorems.Thm_NamesInOrder_everyDirectAlternationMeetsTheBound
-- name    : NamesInOrder.everyDirectAlternationMeetsTheBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:42:35.11552+00:00
-- url     : https://prove2.me/theorems/228401b5-b9ae-4757-9979-94c364c92cb9
-- title:
--   Names In Order: every Direct Alternation Meets The Bound
-- statement:
--   **The main statement**: Corollary 11 from the first sentence of Theorem A (c) and Theorem D (b),
--   for every machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Main.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Main.lean#L31-L31

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

theorem NamesInOrder.everyDirectAlternationMeetsTheBound : EveryDirectAlternationMeetsTheBound := by sorry
