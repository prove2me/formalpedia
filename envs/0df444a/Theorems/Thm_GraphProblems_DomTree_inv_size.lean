-- Prove2me | Theorems.Thm_GraphProblems_DomTree_inv_size
-- name    : GraphProblems.DomTree.inv_size
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:03:01.345463+00:00
-- url     : https://prove2.me/theorems/f795dc46-3d34-42e7-a48d-d264d073dc5a
-- title:
--   Dom Tree: inv size
-- statement:
--   What the invariant says on the size of a node.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L200-L207
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L200-L207

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}

theorem GraphProblems.DomTree.inv_size {n s w : ℕ} {x : DNode} {p t : ℕ} (h : Inv n s w x p t) :
    x.1 = (List.replicate n (), s) ∧ x.2.1.length ≤ n ∧ (∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < n) ∧ x.2.2.length ≤ 2 * n ∧
      Shaped w n x.2.2 ∧ x.2.1.length + x.2.2.length ≤ 3 * n := by sorry
