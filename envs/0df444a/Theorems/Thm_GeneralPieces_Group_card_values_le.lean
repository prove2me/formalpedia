-- Prove2me | Theorems.Thm_GeneralPieces_Group_card_values_le
-- name    : GeneralPieces.Group.card_values_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:58.601029+00:00
-- url     : https://prove2.me/theorems/a4a28d6d-f23b-4694-9fdf-f6b2c4aaa25b
-- title:
--   Group: card values le
-- statement:
--   "Each a product of at most g² values": the nodes of a group, the pairs of nodes inside it, and
--   the pairs of one node inside and one outside, are at most g² in all.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L79-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L79-L99

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

theorem GeneralPieces.Group.card_values_le [Fintype J] [LinearOrder J] [Fintype J'] [DecidableEq J'] (χ : J → J') (G : J') :
    #{a | χ a = G} + #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G} + ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'} ≤ Fintype.card J ^ 2 := by sorry
