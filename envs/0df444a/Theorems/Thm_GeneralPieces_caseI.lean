-- Prove2me | Theorems.Thm_GeneralPieces_caseI
-- name    : GeneralPieces.caseI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:06.340693+00:00
-- url     : https://prove2.me/theorems/8daff4ad-ffa7-446b-b0d0-2f15d90fa227
-- title:
--   General Pieces: case I
-- statement:
--   Case (i): g = 3K⁸ and ζ = 1/(2K). If the numbers c_{a,b} are symmetric and every node shares at
--   most P bits in all, some grouping has fewer than 2g/K nodes in every group and
--   Y ≤ (U + 2ζgP)/K² = (U + gP/K)/K² for any two groups. The proof is
--   `Groundwork.Colouring.exists_colouring`, which has a natural number P; a real P is rounded down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseI.lean#L29-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseI.lean#L29-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_CaseI
set_option autoImplicit false
section
section
open GeneralPieces
open Finset

theorem GeneralPieces.caseI (K g : ℕ) (c : Fin g → Fin g → ℕ) (P ζ : ℝ) (hK : 2 ≤ K) (hg : g = 3 * K ^ 8) (hζ : ζ = 1 / (2 * K)) (hs : ∀ a b, c a b = c b a)
    (hP : ∀ a, ∑ b ∈ univ.erase a, (c a b : ℝ) ≤ P) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) ≤
        ((∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + 2 * ζ * g * P) / (K : ℝ) ^ 2 := by sorry
