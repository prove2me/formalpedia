-- Prove2me | Theorems.Thm_GeneralPieces_Group_exp_le_inv
-- name    : GeneralPieces.Group.exp_le_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:18.653573+00:00
-- url     : https://prove2.me/theorems/5a8e8bae-7eb1-4a23-8918-802274bb756f
-- title:
--   Group: exp le inv
-- statement:
--   "Which for j = g/K is at most 1/(2gK)", because 2ζ²g ≥ K·ln(2gK).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L66-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L66-L75

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

theorem GeneralPieces.Group.exp_le_inv (hK : 1 ≤ K) (hn : 1 ≤ n) {ζ : ℝ} (h : (K : ℝ) * Real.log (2 * ((K * n : ℕ) : ℝ) * K) ≤ 2 * ζ ^ 2 * ((K * n : ℕ) : ℝ)) :
    Real.exp (-(2 * n * ζ ^ 2)) ≤ 1 / (2 * ((K * n : ℕ) : ℝ) * K) := by sorry
