-- Prove2me | Theorems.Thm_GeneralPieces_Group_cls_eq
-- name    : GeneralPieces.Group.cls_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:37:29.026093+00:00
-- url     : https://prove2.me/theorems/d597145a-a043-4435-91cf-6a4a57090ea9
-- title:
--   Group: cls eq
-- statement:
--   The group number γ of the grouping χ₀∘e, written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L34-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L34-L36

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

theorem GeneralPieces.Group.cls_eq (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : cls e γ = ({a | chi0 (e a) = γ} : Finset (Fin (K * n))) := by sorry
