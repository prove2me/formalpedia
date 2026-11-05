-- Prove2me | Theorems.Thm_GeneralPieces_Group_event_first_kind
-- name    : GeneralPieces.Group.event_first_kind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:14.197434+00:00
-- url     : https://prove2.me/theorems/b719e08c-dd60-44a3-a63e-34f4272faa1f
-- title:
--   Group: event first kind
-- statement:
--   The event of the first kind, one for each group γ: "apply the inequality to Σ_{a ∈ G_γ} c_a,
--   with R = P and expectation U/K". The event Σ_{a ∈ G_γ} c_a ≥ (U + ζgP)/K has at most the
--   fraction exp(−2(g/K)ζ²) of all e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L124-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L124-L132

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

theorem GeneralPieces.Group.event_first_kind (hK : 1 ≤ K) (hn : 1 ≤ n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (hζ : 0 ≤ ζ) (hP0 : 0 < P)
    (hP : ∀ a, cs c a ≤ P) (γ : Fin K) :
    (#{e : Equiv.Perm (Fin (K * n)) | (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K ≤ ∑ a ∈ cls e γ, cs c a} : ℝ) ≤
      Real.exp (-(2 * n * ζ ^ 2)) * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by sorry
