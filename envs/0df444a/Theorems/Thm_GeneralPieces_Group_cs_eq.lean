-- Prove2me | Theorems.Thm_GeneralPieces_Group_cs_eq
-- name    : GeneralPieces.Group.cs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:38:07.799893+00:00
-- url     : https://prove2.me/theorems/00523bf1-ca55-4061-99cf-b4e4dd3a0d33
-- title:
--   Group: cs eq
-- statement:
--   c_a is the sum of c_{a,b} over the nodes b ≠ a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L112-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L112-L114

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

theorem GeneralPieces.Group.cs_eq {g : ℕ} (c : Fin g → Fin g → ℕ) (a : Fin g) : cs c a = ∑ b ∈ univ.erase a, (c a b : ℝ) := by sorry
