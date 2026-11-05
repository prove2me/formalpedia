-- Prove2me | Theorems.Thm_GeneralPieces_Group_display_left
-- name    : GeneralPieces.Group.display_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:27.157235+00:00
-- url     : https://prove2.me/theorems/e6a4058a-cd7c-4f32-b929-88c52123e11e
-- title:
--   Group: display left
-- statement:
--   The first inequality of the display, "summing the second bound over the g/K nodes a ∈ G_γ, where
--   γ ≠ γ'": Y_{γ,γ'} < (1/K)·Σ_{a ∈ G_γ} c_a + (g/K)·(ζP/K).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L217-L230
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L217-L230

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

theorem GeneralPieces.Group.display_left (hn : 1 ≤ n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (e : Equiv.Perm (Fin (K * n)))
    (h2 : ∀ a γ', ∑ b ∈ cls e γ', cz c a b < (cs c a + ζ * P) / K) {γ γ' : Fin K} (hne : γ ≠ γ') :
    Yg c e γ γ' < 1 / K * ∑ a ∈ cls e γ, cs c a + ((K * n : ℕ) : ℝ) / K * (ζ * P / K) := by sorry
