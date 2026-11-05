-- Prove2me | Theorems.Thm_GraphProblems_DomTree_card_filter_split
-- name    : GraphProblems.DomTree.card_filter_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:02:32.266906+00:00
-- url     : https://prove2.me/theorems/8e9ec287-253b-4cd4-a10c-2aacf151ad53
-- title:
--   Dom Tree: card filter split
-- statement:
--   A set that is cut in two by a property Q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L103-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L103-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}

theorem GraphProblems.DomTree.card_filter_split {α : Type} [Fintype α] (P Pl Ph Q : α → Prop) [DecidablePred P] [DecidablePred Pl] [DecidablePred Ph]
    (hl : ∀ a, Pl a ↔ P a ∧ Q a) (hh : ∀ a, Ph a ↔ P a ∧ ¬Q a) :
    #(univ.filter P) = #(univ.filter Pl) + #(univ.filter Ph) := by sorry
