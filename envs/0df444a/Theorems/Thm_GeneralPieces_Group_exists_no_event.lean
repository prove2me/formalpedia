-- Prove2me | Theorems.Thm_GeneralPieces_Group_exists_no_event
-- name    : GeneralPieces.Group.exists_no_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:14.402053+00:00
-- url     : https://prove2.me/theorems/a4228f3b-b08e-4e59-ab69-ad61fb7f16a7
-- title:
--   Group: exists no event
-- statement:
--   "So for some χ none of them occurs. For this χ we have Σ_{a ∈ G_γ} c_a < (U + ζgP)/K and Σ_{b ∈
--   G_γ'} c_{a,b} < (c_a + ζP)/K for all γ, γ' and a."
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L161-L208
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L161-L208

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

theorem GeneralPieces.Group.exists_no_event (hK : 1 ≤ K) (hn : 1 ≤ n) (hg : 2 ≤ K * n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (hζ : 0 ≤ ζ) (hP0 : 0 < P)
    (hP : ∀ a, cs c a ≤ P) (hPg : ∀ a b, a ≠ b → (c a b : ℝ) ≤ P / ((K * n : ℕ) : ℝ))
    (hH : (K : ℝ) * Real.log (2 * ((K * n : ℕ) : ℝ) * K) ≤ 2 * ζ ^ 2 * ((K * n : ℕ) : ℝ)) :
    ∃ e : Equiv.Perm (Fin (K * n)), (∀ γ, ∑ a ∈ cls e γ, cs c a < (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K) ∧
      ∀ a γ', ∑ b ∈ cls e γ', cz c a b < (cs c a + ζ * P) / K := by sorry
