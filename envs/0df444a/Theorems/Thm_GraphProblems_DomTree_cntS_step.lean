-- Prove2me | Theorems.Thm_GraphProblems_DomTree_cntS_step
-- name    : GraphProblems.DomTree.cntS_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:02:37.206429+00:00
-- url     : https://prove2.me/theorems/2dc13de8-fb65-4497-8842-8eec5de2ca34
-- title:
--   Dom Tree: cnt S step
-- statement:
--   The number of a node is the sum of the numbers of its two children.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L111-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L111-L123

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

theorem GraphProblems.DomTree.cntS_step {w : ℕ} {x l h : DNode} (e : stepD w x = some (l, h)) (n s : ℕ) :
    cntS n s (leafD x).2.2 = cntS n s (leafD l).2.2 + cntS n s (leafD h).2.2 := by sorry
