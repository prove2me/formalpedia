-- Prove2me | Theorems.Thm_GeneralPieces_Group_card_events_lt
-- name    : GeneralPieces.Group.card_events_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:23.418422+00:00
-- url     : https://prove2.me/theorems/fc68d2e5-99e7-45ba-be4d-598314c8b1f0
-- title:
--   Group: card events lt
-- statement:
--   "These are (g+1)K < 2gK events."
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L156-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L156-L157

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}

theorem GeneralPieces.Group.card_events_lt {K g : ℕ} (hK : 1 ≤ K) (hg : 2 ≤ g) : (g + 1) * K < 2 * g * K := by sorry
