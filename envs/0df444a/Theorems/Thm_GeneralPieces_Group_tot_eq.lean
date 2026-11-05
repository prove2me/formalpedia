-- Prove2me | Theorems.Thm_GeneralPieces_Group_tot_eq
-- name    : GeneralPieces.Group.tot_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:15.935911+00:00
-- url     : https://prove2.me/theorems/af08b7d2-4144-4cc2-9ea5-18b7fa5c1ccb
-- title:
--   Group: tot eq
-- statement:
--   U is the sum of c_{a,b} over the ordered pairs of different nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L117-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L117-L117

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

theorem GeneralPieces.Group.tot_eq {g : ℕ} (c : Fin g → Fin g → ℕ) : tot c = ∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ) := by sorry
