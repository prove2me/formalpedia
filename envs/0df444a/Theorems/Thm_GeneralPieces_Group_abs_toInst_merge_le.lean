-- Prove2me | Theorems.Thm_GeneralPieces_Group_abs_toInst_merge_le
-- name    : GeneralPieces.Group.abs_toInst_merge_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:58.603218+00:00
-- url     : https://prove2.me/theorems/d74c22e5-7ead-466f-8e2d-b158036e3217
-- title:
--   Group: abs to Inst merge le
-- statement:
--   "The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} = 2^{2gP/K} terms, each a product of at most
--   g² values": if every group has at most m nodes, an entry of a table of the clique is at most
--   2^{Pm + g²B} in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L104-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L104-L141

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
variable {J J' σ τ A : Type*}

theorem GeneralPieces.Group.abs_toInst_merge_le [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] [DecidableEq A] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    (D : J' → J' → Finset A) (dec : J' → J' → A → (J × J → τ)) {P B m : ℕ} (h : N.Sized P B) (hm : ∀ G, #{a | χ a = G} ≤ m) (G : J') (θ : J' → A) :
    |(N.merge χ s₀ t₀).toInst D dec G θ| ≤ 2 ^ (P * m + B * Fintype.card J ^ 2) := by sorry
