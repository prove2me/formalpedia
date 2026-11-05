-- Prove2me | Theorems.Thm_GeneralPieces_Group_event_second_kind
-- name    : GeneralPieces.Group.event_second_kind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:18.923218+00:00
-- url     : https://prove2.me/theorems/437febaf-17a6-46c4-bc62-1e31e48acbe9
-- title:
--   Group: event second kind
-- statement:
--   The event of the second kind, one for each node a and each group γ': "apply the inequality to
--   Σ_{b ∈ G_γ'} c_{a,b}, with R = P/g and expectation c_a/K". The event
--   Σ_{b ∈ G_γ'} c_{a,b} ≥ (c_a + ζP)/K has at most the fraction exp(−2(g/K)ζ²) of all e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L137-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L137-L151

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

theorem GeneralPieces.Group.event_second_kind (hK : 1 ≤ K) (hn : 1 ≤ n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (hζ : 0 ≤ ζ) (hP0 : 0 < P)
    (hPg : ∀ a b, a ≠ b → (c a b : ℝ) ≤ P / ((K * n : ℕ) : ℝ)) (a : Fin (K * n)) (γ' : Fin K) :
    (#{e : Equiv.Perm (Fin (K * n)) | (cs c a + ζ * P) / K ≤ ∑ b ∈ cls e γ', cz c a b} : ℝ) ≤
      Real.exp (-(2 * n * ζ ^ 2)) * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by sorry
