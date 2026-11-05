-- Prove2me | Theorems.Thm_GeneralPieces_Group_card_group
-- name    : GeneralPieces.Group.card_group
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:06.764821+00:00
-- url     : https://prove2.me/theorems/2e8400ea-6012-4842-83dd-9605a36151ce
-- title:
--   Group: card group
-- statement:
--   "Let χ be uniformly random among the groupings in which every group has exactly g/K nodes":
--   every grouping χ₀∘e has exactly n = g/K nodes in every group.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L40-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L40-L40

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

theorem GeneralPieces.Group.card_group (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : #{a | chi0 (e a) = γ} = n := by sorry
