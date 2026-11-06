-- Prove2me | Theorems.Thm_OccurM_everyWrapperCounts
-- name    : OccurM.everyWrapperCounts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:11:11.393772+00:00
-- url     : https://prove2.me/theorems/91205fe7-c0b7-4bde-a8d4-b9a62980a459
-- title:
--   Occur M: every Wrapper Counts
-- statement:
--   Every machine that runs a preparation and then a machine that counts within the bound
--   `SatM.bound` on formulas in which every variable occurs counts within the printed bound on every
--   k-CNF with k ≥ 1 and m ≥ 2; compact code.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Wrapper.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Wrapper.lean#L56-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_OccurM_Wrapper
set_option autoImplicit false
section
section
open OccurM
open Groundwork Turing MainTheoremForms ClausesOccur
open Sat3 (CNF)

theorem OccurM.everyWrapperCounts : EveryWrapperCounts := by sorry
