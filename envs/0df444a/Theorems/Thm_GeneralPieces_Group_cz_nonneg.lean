-- Prove2me | Theorems.Thm_GeneralPieces_Group_cz_nonneg
-- name    : GeneralPieces.Group.cz_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:37:56.248919+00:00
-- url     : https://prove2.me/theorems/6a37187e-b487-4475-a51e-1d78bedca668
-- title:
--   Group: cz nonneg
-- statement:
--   The Group construction uses the cz nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L104-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L104-L107

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

theorem GeneralPieces.Group.cz_nonneg {g : ℕ} (c : Fin g → Fin g → ℕ) (a b : Fin g) : 0 ≤ cz c a b := by sorry
