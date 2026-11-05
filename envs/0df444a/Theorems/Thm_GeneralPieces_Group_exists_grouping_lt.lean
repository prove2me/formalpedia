-- Prove2me | Theorems.Thm_GeneralPieces_Group_exists_grouping_lt
-- name    : GeneralPieces.Group.exists_grouping_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:38:56.565077+00:00
-- url     : https://prove2.me/theorems/75aaf0ae-e142-4f41-8652-965697e4b3a2
-- title:
--   Group: exists grouping lt
-- statement:
--   "Some grouping has at most 2g/K nodes in every group and Y ≤ L for all γ ≠ γ'", in both cases,
--   with fewer than 2g/K nodes in every group. Here P = 0 is allowed: then no two nodes share a bit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L39-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L39-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_Lemma
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset Groundwork

theorem GeneralPieces.Group.exists_grouping_lt (K g : ℕ) (ζ : ℝ) (P : ℕ) (c : Fin g → Fin g → ℕ) (hK : 2 ≤ K) (hg : 2 ≤ g) (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hs : ∀ a b, c a b = c b a) (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) (h : AppRunningTime.Cases K g ζ P c) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → ∑ a with χ a = γ, ∑ b with χ b = γ', c a b ≤ AppRunningTime.Lof K g ζ P (∑ a, ∑ b ∈ univ.erase a, c a b) := by sorry
