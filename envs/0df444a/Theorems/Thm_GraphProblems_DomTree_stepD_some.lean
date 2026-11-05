-- Prove2me | Theorems.Thm_GraphProblems_DomTree_stepD_some
-- name    : GraphProblems.DomTree.stepD_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:12:13.176578+00:00
-- url     : https://prove2.me/theorems/f7f52702-e2c2-4938-8360-9adfa8db06fd
-- title:
--   Dom Tree: step D some
-- statement:
--   What `stepD` returns.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L91-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L91-L100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
import Theorems.Thm_Groundwork_PolyT_contains
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}

theorem GraphProblems.DomTree.stepD_some {w : ℕ} {x l h : DNode} (e : stepD w x = some (l, h)) :
    ∃ C ∈ x.2.1, w < C.length ∧
      l = (x.1, (x.2.1.filter fun D => D != C, posC (C.take w) :: x.2.2)) ∧
      h = (x.1, (x.2.1.map fun D => D.filter fun u => !(C.take w).contains u, ((C.take w).map fun u => [(u, false)]) ++ x.2.2)) := by sorry
