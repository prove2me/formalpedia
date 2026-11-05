-- Prove2me | Theorems.Thm_GraphProblems_DomTree_inv_bound
-- name    : GraphProblems.DomTree.inv_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:03:11.770784+00:00
-- url     : https://prove2.me/theorems/5d92562e-67ec-43cc-ad6a-cb471994ec9d
-- title:
--   Dom Tree: inv bound
-- statement:
--   The Dom Tree construction uses the inv bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L146-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L146-L148

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}

theorem GraphProblems.DomTree.inv_bound {n s w : ℕ} (x : DNode) (p t : ℕ) (h : Inv n s w x p t) : p ≤ 2 * n ∧ t ≤ n := by sorry
