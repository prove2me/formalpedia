-- Prove2me | Theorems.Thm_GeneralPieces_Group_group_tail
-- name    : GeneralPieces.Group.group_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:37:34.075662+00:00
-- url     : https://prove2.me/theorems/d0398f68-06a3-41b6-9c2a-d28662a0ff02
-- title:
--   Group: group tail
-- statement:
--   Hoeffding's inequality for the sum of a list x of numbers in [0, R] over the group number γ: its
--   expectation is (Σ x)/K, and j = n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L79-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L79-L91

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

theorem GeneralPieces.Group.group_tail (hK : 1 ≤ K) (hn : 1 ≤ n) (x : Fin (K * n) → ℝ) {R ζ : ℝ} (hR : 0 < R) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ R) (hζ : 0 ≤ ζ) (γ : Fin K) :
    (#{e : Equiv.Perm (Fin (K * n)) | (∑ i, x i) / K + ζ * n * R ≤ ∑ i ∈ cls e γ, x i} : ℝ) ≤
      Real.exp (-(2 * n * ζ ^ 2)) * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by sorry
