-- Prove2me | Theorems.Thm_GeneralPieces_Group_display_right
-- name    : GeneralPieces.Group.display_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:26.804215+00:00
-- url     : https://prove2.me/theorems/453bc383-80cc-47fb-8e96-d2604ec026cd
-- title:
--   Group: display right
-- statement:
--   The second inequality of the display, "inserting the first": (1/K)·Σ_{a ∈ G_γ} c_a +
--   (g/K)·(ζP/K) < (U + 2ζgP)/K².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L234-L244
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L234-L244

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

theorem GeneralPieces.Group.display_right (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (e : Equiv.Perm (Fin (K * n)))
    (h1 : ∀ γ, ∑ a ∈ cls e γ, cs c a < (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K) (γ : Fin K) :
    1 / K * ∑ a ∈ cls e γ, cs c a + ((K * n : ℕ) : ℝ) / K * (ζ * P / K) < (tot c + 2 * ζ * ((K * n : ℕ) : ℝ) * P) / (K : ℝ) ^ 2 := by sorry
