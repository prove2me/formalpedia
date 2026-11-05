-- Prove2me | Theorems.Thm_GraphProblems_DomTree_sat_heavy
-- name    : GraphProblems.DomTree.sat_heavy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:02:11.660458+00:00
-- url     : https://prove2.me/theorems/531565e0-ed6a-4d01-b5f8-883ae0eca238
-- title:
--   Dom Tree: sat heavy
-- statement:
--   The heavy child: the node, and no variable of H is true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L71-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L71-L86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
import Theorems.Thm_Groundwork_PolyT_contains
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}

theorem GraphProblems.DomTree.sat_heavy {O : List (List ℕ)} {F : Fml} {H : List ℕ} :
    Sat a ((O.map fun D => D.filter fun u => !H.contains u).map posC ++ ((H.map fun u => [(u, false)]) ++ F)) ↔
      Sat a (O.map posC ++ F) ∧ ¬Hit a H := by sorry
