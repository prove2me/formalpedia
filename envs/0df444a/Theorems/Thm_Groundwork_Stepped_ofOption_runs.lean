-- Prove2me | Theorems.Thm_Groundwork_Stepped_ofOption_runs
-- name    : Groundwork.Stepped.ofOption_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:25:19.366068+00:00
-- url     : https://prove2.me/theorems/1ae36858-9558-4009-adf7-bb28ce331c32
-- title:
--   Stepped: of Option runs
-- statement:
--   Where g has a value, `ofOption g` returns it in one step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L25-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L25-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Comb
set_option autoImplicit false
section
section
open Groundwork Groundwork.Stepped
variable {α β : Type}

theorem Groundwork.Stepped.ofOption_runs [HasSize α] [HasSize β] {g : α → Option β} {a : α} {b : β} (h : g a = some b) :
    (ofOption g).Runs a 1 (max (size a) (size b) + 1) b := by sorry
